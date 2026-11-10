module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.Algebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem

/-!
# The Mittag-Leffler criterion for canonical extension

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U` and let `M = limₙ H⁰(U, F_n)` be its module of compatible global sections. If the inverse
system of sections satisfies the Mittag-Leffler condition, the limit topology on `M` is its
`I`-adic topology, and every projection `M → H⁰(U, F_n)` has finite image, then `(F_n)`
canonically extends to `X`.

## Main definitions

* `Stacks.Algebraization.quotientModule` — the quotient `M/Iⁿ⁺¹M`.
* `Stacks.Algebraization.canonicalComparison` — the canonical map from `(M/Iⁿ⁺¹M)^~|_U` to the
  `n`-th term of the system, together with its action on sections coming from `M`.

## Main results

* `Stacks.Algebraization.epi_canonicalComparison_of_mittagLeffler` — Stacks 0EHF: the canonical
  maps `(M/Iⁿ⁺¹M)^~|_U ⟶ F_n` are surjective.
* `Stacks.Algebraization.canonicallyExtends_of_finite_limit_images` — Stacks 0EHH.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: term `n` is the source's `F_{n+1}`.

Mittag-Leffler together with the agreement of the two topologies makes `{M/IⁿM}` and
`{H⁰(U, F_n)}` pro-isomorphic, so the candidate extension is `G_n = (M/IⁿM)^~`; it is coherent
because the projections have finite image, which by Stacks 031D makes `M` finite over the
`I`-adic completion of `A`.

Canonical extension is the conclusion Stacks 0EHH asserts. The source adds, as a corollary over
an `I`-adically complete ring, that `(F_n)` is then the completion of a coherent `𝒪_U`-module;
that "in particular" clause is proved separately, in
`Stacks.Algebraization.essImage_completionFunctor_of_finite_limit_images`
(`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerAlgebraization`),
using part (2) of Stacks 0EIR and the chain of Stacks 0EIL.

Pro-isomorphism of the two inverse systems is checked through the presheaf of maps out of a cone
vertex that factor through some stage, which makes it readable off cone data: two cones with the
same vertex and mutually cofinal factorizations have isomorphic Yoneda colimits. The comparison
is made in `ModuleCat A` and transported to quasi-coherent sheaves along Mathlib's
`AlgebraicGeometry.tildeEquiv`.

## References

* [The Stacks Project, Lemma 52.11.5 (0EHH)](https://stacks.math.columbia.edu/tag/0EHH)
* [The Stacks Project, Definition 52.11.3 (0EIP)](https://stacks.math.columbia.edu/tag/0EIP)
* [The Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [The Stacks Project, Lemma 10.97.1 (031D)](https://stacks.math.columbia.edu/tag/031D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Filter
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section ProComparison

universe v w

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]

private def coneFactorFunctor {F : J ⥤ C} (c : Cone F) : Cᵒᵖᵒᵖ ⥤ Type v where
  obj Y := { f : c.pt ⟶ Y.unop.unop // ∃ j, ∃ g : F.obj j ⟶ Y.unop.unop,
    c.π.app j ≫ g = f }
  map f := ↾fun x => ⟨x.val ≫ f.unop.unop, by
    obtain ⟨j, g, hg⟩ := x.property
    exact ⟨j, g ≫ f.unop.unop, by rw [← Category.assoc, hg]⟩⟩
  map_id := by
    intro X
    ext x
    simp
  map_comp := by
    intro X Y Z f g
    ext x
    simp

private def coneFactorCocone {F : J ⥤ C} (c : Cone F) :
    Cocone (F.op ⋙ yoneda) where
  pt := coneFactorFunctor c
  ι := {
    app := fun j => {
      app := fun Y => ↾fun x => ⟨c.π.app j.unop ≫ x.unop, ⟨j.unop, x.unop, rfl⟩⟩
      naturality := by
        intro X Y f
        ext x
        apply Subtype.ext
        simp [coneFactorFunctor]
    }
    naturality := by
      intro i j f
      ext Y x
      apply Subtype.ext
      change c.π.app j.unop ≫ (F.map f.unop ≫ x.unop) = c.π.app i.unop ≫ x.unop
      rw [← Category.assoc, c.w f.unop]
  }

private def coneFactorIsColimit {F : J ⥤ C} (c : Cone F)
    (h : ∀ (i j : J) (Y : C) (f : F.obj i ⟶ Y) (g : F.obj j ⟶ Y),
      c.π.app i ≫ f = c.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), F.map a ≫ f = F.map b ≫ g) :
    IsColimit (coneFactorCocone c) := by
  apply evaluationJointlyReflectsColimits
  intro Y
  apply Types.FilteredColimit.isColimitOf
  · intro x
    obtain ⟨j, g, hg⟩ := x.property
    refine ⟨op j, g.op, ?_⟩
    exact Subtype.ext hg.symm
  · intro i j f g he
    obtain ⟨k, a, b, hab⟩ := h i.unop j.unop Y.unop.unop f.unop g.unop
      (congrArg Subtype.val he)
    refine ⟨op k, a.op, b.op, ?_⟩
    exact congrArg Quiver.Hom.op hab

private def coneFactorIso {F G : J ⥤ C} (c : Cone F) (d : Cone G)
    (e : c.pt ≅ d.pt)
    (hcd : ∀ i, ∃ j, ∃ f : G.obj j ⟶ F.obj i,
      d.π.app j ≫ f = e.inv ≫ c.π.app i)
    (hdc : ∀ j, ∃ i, ∃ f : F.obj i ⟶ G.obj j,
      c.π.app i ≫ f = e.hom ≫ d.π.app j) :
    coneFactorFunctor c ≅ coneFactorFunctor d where
  hom := {
    app := fun Y => ↾fun x => ⟨e.inv ≫ x.val, by
      obtain ⟨i, g, hg⟩ := x.property
      obtain ⟨j, f, hf⟩ := hcd i
      exact ⟨j, f ≫ g, by rw [← Category.assoc, hf, Category.assoc, hg]⟩⟩
    naturality := by
      intro X Y f
      ext x
      apply Subtype.ext
      change e.inv ≫ (x.val ≫ f.unop.unop) = (e.inv ≫ x.val) ≫ f.unop.unop
      exact (Category.assoc _ _ _).symm
  }
  inv := {
    app := fun Y => ↾fun x => ⟨e.hom ≫ x.val, by
      obtain ⟨j, g, hg⟩ := x.property
      obtain ⟨i, f, hf⟩ := hdc j
      exact ⟨i, f ≫ g, by rw [← Category.assoc, hf, Category.assoc, hg]⟩⟩
    naturality := by
      intro X Y f
      ext x
      apply Subtype.ext
      change e.hom ≫ (x.val ≫ f.unop.unop) = (e.hom ≫ x.val) ≫ f.unop.unop
      exact (Category.assoc _ _ _).symm
  }
  hom_inv_id := by
    ext Y x
    apply Subtype.ext
    change e.hom ≫ (e.inv ≫ x.val) = x.val
    simp
  inv_hom_id := by
    ext Y x
    apply Subtype.ext
    change e.inv ≫ (e.hom ≫ x.val) = x.val
    simp

private def colimitYonedaIsoOfCones {F G : J ⥤ C} (c : Cone F) (d : Cone G)
    [HasColimit (F.op ⋙ yoneda)] [HasColimit (G.op ⋙ yoneda)]
    (e : c.pt ≅ d.pt)
    (hc : ∀ (i j : J) (Y : C) (f : F.obj i ⟶ Y) (g : F.obj j ⟶ Y),
      c.π.app i ≫ f = c.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), F.map a ≫ f = F.map b ≫ g)
    (hd : ∀ (i j : J) (Y : C) (f : G.obj i ⟶ Y) (g : G.obj j ⟶ Y),
      d.π.app i ≫ f = d.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), G.map a ≫ f = G.map b ≫ g)
    (hcd : ∀ i, ∃ j, ∃ f : G.obj j ⟶ F.obj i,
      d.π.app j ≫ f = e.inv ≫ c.π.app i)
    (hdc : ∀ j, ∃ i, ∃ f : F.obj i ⟶ G.obj j,
      c.π.app i ≫ f = e.hom ≫ d.π.app j) :
    colimit (F.op ⋙ yoneda) ≅ colimit (G.op ⋙ yoneda) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (coneFactorIsColimit c hc) ≪≫
    coneFactorIso c d e hcd hdc ≪≫
    (coneFactorIsColimit d hd).coconePointUniqueUpToIso (colimit.isColimit _)

private theorem cone_detects_eventual_equality_map
    {D : Type*} [Category D] (E : C ≌ D) {F : J ⥤ C} (c : Cone F)
    (hc : ∀ (i j : J) (Y : C) (f : F.obj i ⟶ Y) (g : F.obj j ⟶ Y),
      c.π.app i ≫ f = c.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), F.map a ≫ f = F.map b ≫ g)
    (i j : J) (Y : D) (f : (F ⋙ E.functor).obj i ⟶ Y)
    (g : (F ⋙ E.functor).obj j ⟶ Y)
    (h : (E.functor.mapCone c).π.app i ≫ f =
      (E.functor.mapCone c).π.app j ≫ g) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F ⋙ E.functor).map a ≫ f = (F ⋙ E.functor).map b ≫ g := by
  let f' := E.functor.preimage (f ≫ (E.counitIso.app Y).inv)
  let g' := E.functor.preimage (g ≫ (E.counitIso.app Y).inv)
  have hf : E.functor.map f' = f ≫ (E.counitIso.app Y).inv :=
    E.functor.map_preimage _
  have hg : E.functor.map g' = g ≫ (E.counitIso.app Y).inv :=
    E.functor.map_preimage _
  have hh : c.π.app i ≫ f' = c.π.app j ≫ g' := by
    apply E.functor.map_injective
    simp only [Functor.map_comp, hf, hg, ← Category.assoc]
    exact congrArg (fun t => t ≫ (E.counitIso.app Y).inv) h
  obtain ⟨k, a, b, hab⟩ := hc i j (E.inverse.obj Y) f' g' hh
  refine ⟨k, a, b, ?_⟩
  apply (cancel_mono (E.counitIso.app Y).inv).mp
  simpa only [Functor.comp_map, Functor.map_comp, hf, hg, Category.assoc] using
    congrArg E.functor.map hab

private def colimitYonedaIsoOfMappedCones
    {D : Type*} [Category D] (E : C ≌ D) {F G : J ⥤ C}
    (c : Cone F) (d : Cone G)
    [HasColimit ((F ⋙ E.functor).op ⋙ yoneda)]
    [HasColimit ((G ⋙ E.functor).op ⋙ yoneda)]
    (e : c.pt ≅ d.pt)
    (hc : ∀ (i j : J) (Y : C) (f : F.obj i ⟶ Y) (g : F.obj j ⟶ Y),
      c.π.app i ≫ f = c.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), F.map a ≫ f = F.map b ≫ g)
    (hd : ∀ (i j : J) (Y : C) (f : G.obj i ⟶ Y) (g : G.obj j ⟶ Y),
      d.π.app i ≫ f = d.π.app j ≫ g →
        ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), G.map a ≫ f = G.map b ≫ g)
    (hcd : ∀ i, ∃ j, ∃ f : G.obj j ⟶ F.obj i,
      d.π.app j ≫ f = e.inv ≫ c.π.app i)
    (hdc : ∀ j, ∃ i, ∃ f : F.obj i ⟶ G.obj j,
      c.π.app i ≫ f = e.hom ≫ d.π.app j) :
    colimit ((F ⋙ E.functor).op ⋙ yoneda) ≅
      colimit ((G ⋙ E.functor).op ⋙ yoneda) := by
  apply colimitYonedaIsoOfCones (E.functor.mapCone c) (E.functor.mapCone d)
    (E.functor.mapIso e) (cone_detects_eventual_equality_map E c hc)
    (cone_detects_eventual_equality_map E d hd)
  · intro i
    obtain ⟨j, f, hf⟩ := hcd i
    exact ⟨j, E.functor.map f, by simpa using congrArg E.functor.map hf⟩
  · intro j
    obtain ⟨i, f, hf⟩ := hdc j
    exact ⟨i, E.functor.map f, by simpa using congrArg E.functor.map hf⟩

private theorem cone_detects_eventual_equality_of_epi
    {F : ℕᵒᵖ ⥤ C} (c : Cone F) (hc : ∀ i, Epi (c.π.app i))
    (i j : ℕᵒᵖ) (Y : C) (f : F.obj i ⟶ Y) (g : F.obj j ⟶ Y)
    (h : c.π.app i ≫ f = c.π.app j ≫ g) :
    ∃ (k : ℕᵒᵖ) (a : k ⟶ i) (b : k ⟶ j), F.map a ≫ f = F.map b ≫ g := by
  let k := op (max i.unop j.unop)
  let a : k ⟶ i := (homOfLE (Nat.le_max_left _ _)).op
  let b : k ⟶ j := (homOfLE (Nat.le_max_right _ _)).op
  have := hc k
  refine ⟨k, a, b, (cancel_epi (c.π.app k)).mp ?_⟩
  simpa only [← Category.assoc, c.w] using h

end ProComparison

private theorem diagramToPro_iso_of_colimitYonedaIso
    {X : Scheme.{u}} (F G : ℕᵒᵖ ⥤ AlgebraicGeometry.Scheme.QuasicoherentModules X)
    (h : colimit (F.op ⋙ yoneda) ≅ colimit (G.op ⋙ yoneda)) :
    Nonempty (Stacks.Coherent.diagramToPro F ≅ Stacks.Coherent.diagramToPro G) := by
  let e : ℕᵒᵖᵒᵖ ≌ ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) :=
    (Shrink.equivalence.{u} (ℕᵒᵖᵒᵖ)).trans
      (ShrinkHoms.equivalence.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
  let : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :=
    IsFiltered.of_equivalence e
  let D := e.inverse ⋙ F.op
  let E := e.inverse ⋙ G.op
  let a := (Ind.limCompInclusion.app D) ≪≫
    Functor.Final.colimitIso e.inverse (F.op ⋙ yoneda)
  let b := (Ind.limCompInclusion.app E) ≪≫
    Functor.Final.colimitIso e.inverse (G.op ⋙ yoneda)
  exact ⟨((Ind.inclusion (AlgebraicGeometry.Scheme.QuasicoherentModules X)ᵒᵖ).preimageIso
    (a ≪≫ h ≪≫ b.symm)).symm.op⟩

private theorem transitionImage_subobjectModule {A : Type u} [CommRing A]
    (G : ℕᵒᵖ ⥤ ModuleCat.{u} A) (i k : ℕ) (h : i ≤ k) :
    ModuleCat.subobjectModule (G.obj (op i)) (transitionImage G i k h) =
      LinearMap.range (G.map (homOfLE h).op).hom := by
  have heq :
      Subobject.mk (Limits.image.ι (G.map (homOfLE h).op)) =
        Subobject.mk (ModuleCat.ofHom
          (G.map (homOfLE h).op).hom.range.subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange _)
      (ModuleCat.imageIsoRange_hom_subtype _)
  rw [transitionImage, heq]
  exact (ModuleCat.subobjectModule (G.obj (op i))).apply_symm_apply _

private theorem globalSections_mittagLeffler
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G) :
    MittagLeffler.IsMittagLefflerModule
      (fun {_i _j} h => (G.map (homOfLE h).op).hom) := by
  intro i
  obtain ⟨c, hic, hc⟩ := hML i
  refine ⟨c, hic, fun k hck => ?_⟩
  have hr := congrArg (fun Q => ModuleCat.subobjectModule (G.obj (op i)) Q)
    (hc k hck)
  rw [transitionImage_subobjectModule, transitionImage_subobjectModule] at hr
  have hset := congrArg (fun Q : Submodule A (G.obj (op i)) => Q.carrier) hr
  change Set.range (fun x => (G.map (homOfLE (hic.trans hck)).op).hom x) =
    Set.range (fun x => (G.map (homOfLE hic).op).hom x) at hset
  exact hset

private noncomputable def moduleTower
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    DirInvSystem (fun n : ℕ => G.obj (op n)) where
  φ := fun {i j} h => (G.map (homOfLE h).op).hom
  φ_self := by
    intro i x
    change (G.map (𝟙 (op i))).hom x = x
    rw [G.map_id]
    rfl
  φ_comp := by
    intro i j k hij hjk x
    rw [← ModuleCat.comp_apply, ← G.map_comp]
    rfl

/-- The transition maps of a tower of modules form an `InverseSystem`. -/
private theorem inverseSystem_moduleTower {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom) where
  map_self := (moduleTower G).φ_self
  map_map := (moduleTower G).φ_comp

private theorem limitStableFiberProp_map {A : ℕ → Type*}
    (S : DirInvSystem A) (i₀ : ℕ) (x₀ : A i₀)
    {i k : ℕ} (hik : i ≤ k) {x : A k} (hx : Stacks.LocalCohomology.towerFiberProp S i₀ x₀ k x) :
    Stacks.LocalCohomology.towerFiberProp S i₀ x₀ i (S.φ hik x) := by
  by_cases hi : i ≤ i₀
  · by_cases hk : k ≤ i₀
    · have hx' : x = S.φ hk x₀ := by simpa [Stacks.LocalCohomology.towerFiberProp, hk] using hx
      have hcomp := S.φ_comp hik hk x₀
      have heq : hik.trans hk = hi := Subsingleton.elim _ _
      rw [heq] at hcomp
      have hval : S.φ hik x = S.φ hi x₀ := by simpa [hx'] using hcomp
      simpa [Stacks.LocalCohomology.towerFiberProp, hi] using hval
    · have hx' : S.Stable x ∧ S.φ (Nat.le_of_lt (Nat.lt_of_not_ge hk)) x = x₀ := by
        simpa [Stacks.LocalCohomology.towerFiberProp, hk] using hx
      have hki : i₀ ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      have hcomp := S.φ_comp hi hki x
      have heq : hi.trans hki = hik := Subsingleton.elim _ _
      rw [heq, hx'.2] at hcomp
      simpa [Stacks.LocalCohomology.towerFiberProp, hi] using hcomp.symm
  · have hi₀ : i₀ ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hi)
    have hk : ¬ k ≤ i₀ := fun h => hi (le_trans hik h)
    have hk₀ : i₀ ≤ k := hi₀.trans hik
    have hx' : S.Stable x ∧ S.φ hk₀ x = x₀ := by
      simpa [Stacks.LocalCohomology.towerFiberProp, hk] using hx
    have hcomp := S.φ_comp hi₀ hik x
    have heq : hi₀.trans hik = hk₀ := Subsingleton.elim _ _
    rw [heq, hx'.2] at hcomp
    have hval : S.Stable (S.φ hik x) ∧ S.φ hi₀ (S.φ hik x) = x₀ :=
      ⟨DirInvSystem.Stable.map S hik hx'.1, hcomp⟩
    simpa [Stacks.LocalCohomology.towerFiberProp, hi] using hval

private theorem limitStableFiber_transition_surjective {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀)
    {i k : ℕ} (hik : i ≤ k) :
    Function.Surjective (fun z : {x : A k // Stacks.LocalCohomology.towerFiberProp S i₀ x₀ k x} =>
      (⟨S.φ hik z.1, limitStableFiberProp_map S i₀ x₀ hik z.2⟩ :
        {x : A i // Stacks.LocalCohomology.towerFiberProp S i₀ x₀ i x})) := by
  intro z
  by_cases hi : i ≤ i₀
  · by_cases hk : k ≤ i₀
    · have hz : z.1 = S.φ hi x₀ := by
        simpa [Stacks.LocalCohomology.towerFiberProp, hi] using z.2
      refine ⟨⟨S.φ hk x₀, by simp [Stacks.LocalCohomology.towerFiberProp, hk]⟩, ?_⟩
      apply Subtype.ext
      have hcomp := S.φ_comp hik hk x₀
      have heq : hik.trans hk = hi := Subsingleton.elim _ _
      rw [heq] at hcomp
      simpa [hz] using hcomp
    · have h₀k : i₀ ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      have hz : z.1 = S.φ hi x₀ := by
        simpa [Stacks.LocalCohomology.towerFiberProp, hi] using z.2
      obtain ⟨y, hys, hmap⟩ := S.stable_surjective hML h₀k hx₀
      refine ⟨⟨y, by simp [Stacks.LocalCohomology.towerFiberProp, hk, hys, hmap]⟩, ?_⟩
      apply Subtype.ext
      have hcomp := S.φ_comp hi h₀k y
      have heq : hi.trans h₀k = hik := Subsingleton.elim _ _
      rw [heq] at hcomp
      calc
        S.φ hik y = S.φ hi (S.φ h₀k y) := hcomp.symm
        _ = S.φ hi x₀ := by rw [hmap]
        _ = z.1 := hz.symm
  · have hi₀ : i₀ ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hi)
    have hz : S.Stable z.1 ∧ S.φ hi₀ z.1 = x₀ := by
      simpa [Stacks.LocalCohomology.towerFiberProp, hi] using z.2
    obtain ⟨y, hys, hmap⟩ := S.stable_surjective hML hik hz.1
    have h₀k : i₀ ≤ k := hi₀.trans hik
    have hbase : S.φ h₀k y = x₀ :=
      calc
        S.φ h₀k y = S.φ hi₀ (S.φ hik y) := (S.φ_comp hi₀ hik y).symm
        _ = S.φ hi₀ z.1 := by rw [hmap]
        _ = x₀ := hz.2
    have hyprop : Stacks.LocalCohomology.towerFiberProp S i₀ x₀ k y := by
      have hk : ¬ k ≤ i₀ := fun h => hi (le_trans hik h)
      simpa [Stacks.LocalCohomology.towerFiberProp, hk] using And.intro hys hbase
    exact ⟨⟨y, hyprop⟩, Subtype.ext hmap⟩

private noncomputable def limitStableFiberSystem {A : ℕ → Type*}
    (S : DirInvSystem A) (i₀ : ℕ) (x₀ : A i₀) :
    DirInvSystem (fun i => {x : A i // Stacks.LocalCohomology.towerFiberProp S i₀ x₀ i x}) where
  φ := fun {i k} hik x => ⟨S.φ hik x.1, limitStableFiberProp_map S i₀ x₀ hik x.2⟩
  φ_self := by
    intro i x
    exact Subtype.ext (S.φ_self i x.1)
  φ_comp := by
    intro i j k hij hjk x
    exact Subtype.ext (S.φ_comp hij hjk x.1)

private theorem limitStableFiberSystem_mittagLeffler {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀) :
    (limitStableFiberSystem S i₀ x₀).IsMittagLeffler := by
  intro i
  refine ⟨i, le_rfl, fun k hik => ?_⟩
  have h1 : Set.range ((limitStableFiberSystem S i₀ x₀).φ (le_rfl : i ≤ i)) = Set.univ :=
    Set.range_eq_univ.mpr (limitStableFiber_transition_surjective S hML i₀ x₀ hx₀ (le_rfl : i ≤ i))
  have h2 : Set.range ((limitStableFiberSystem S i₀ x₀).φ hik) = Set.univ :=
    Set.range_eq_univ.mpr (limitStableFiber_transition_surjective S hML i₀ x₀ hx₀ hik)
  rw [h1, h2]

private theorem limitStableFiberSystem_nonempty {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀) (i : ℕ) :
    Nonempty {x : A i // Stacks.LocalCohomology.towerFiberProp S i₀ x₀ i x} := by
  by_cases hi : i ≤ i₀
  · exact ⟨⟨S.φ hi x₀, by simp [Stacks.LocalCohomology.towerFiberProp, hi]⟩⟩
  · have hi₀ : i₀ ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hi)
    obtain ⟨x, hx, hmap⟩ := S.stable_surjective hML hi₀ hx₀
    exact ⟨⟨x, by simpa [Stacks.LocalCohomology.towerFiberProp, hi] using And.intro hx hmap⟩⟩

private theorem exists_limit_with_stable_projection
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [HasLimit G]
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G) (j : ℕ) {x : G.obj (op j)}
    (hx : (moduleTower G).Stable x) :
    ∃ z : ToType (limit G), (limit.π G (op j)).hom z = x := by
  let S := moduleTower G
  have hS : S.IsMittagLeffler := by
    intro i
    obtain ⟨c, hic, hc⟩ := globalSections_mittagLeffler G hML i
    refine ⟨c, hic, fun k hck => ?_⟩
    simpa [S, moduleTower] using hc k hck
  let T := limitStableFiberSystem S j x
  have hne : ∀ n, Nonempty
      {y : G.obj (op n) // Stacks.LocalCohomology.towerFiberProp S j x n y} :=
    fun n => limitStableFiberSystem_nonempty S hS j x hx n
  obtain ⟨a, ha⟩ := T.nonempty_limit_of_isMittagLeffler
    (limitStableFiberSystem_mittagLeffler S hS j x hx) hne
  let sec : (G ⋙ forget (ModuleCat.{u} A)).sections :=
    ⟨fun n => (a n.unop).1, by
      intro n m f
      let h : m.unop ≤ n.unop := leOfHom f.unop
      change S.φ h ((a n.unop).1) = (a m.unop).1
      exact congrArg Subtype.val (ha h)⟩
  let L := isLimitOfPreserves (forget (ModuleCat.{u} A)) (limit.isLimit G)
  refine ⟨(Types.isLimitEquivSections L).symm sec, ?_⟩
  have hj : (a j).1 = x := by
    have heq : (a j).1 = S.φ (le_rfl : j ≤ j) x := by
      simpa [Stacks.LocalCohomology.towerFiberProp, T] using (a j).2
    exact heq.trans (S.φ_self j x)
  simpa [L, sec] using (Types.isLimitEquivSections_symm_apply L sec (op j)).trans hj

private theorem projection_range_eq_stable
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [HasLimit G]
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G) (j : ℕ) :
    Set.range (fun z : ToType (limit G) => (limit.π G (op j)).hom z) =
      {x : G.obj (op j) | (moduleTower G).Stable x} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    intro k hjk
    refine ⟨(limit.π G (op k)).hom z, ?_⟩
    have hw := congrArg (fun f => f.hom) (limit.w G (homOfLE hjk).op)
    exact congrArg (fun f => f z) hw
  · exact fun hx => exists_limit_with_stable_projection G hML j hx

private theorem exists_transition_range_eq_projection_range
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G) (i : ℕ) :
    ∃ k : ℕ, ∃ h : i ≤ k,
      Set.range (fun x => (G.map (homOfLE h).op).hom x) =
        Set.range (fun x => (limit.π G (op i)).hom x) := by
  obtain ⟨k, hik, hk⟩ := globalSections_mittagLeffler G hML i
  refine ⟨k, hik, ?_⟩
  rw [projection_range_eq_stable G hML]
  exact ((moduleTower G).stable_eq_range hik hk).symm

section Surjectivity

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable (S : Stacks.Algebraization.AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S))

/-- The ideal of `I 𝒪_U` on an affine open `V` of `U` is the image of `I` under
`A → Γ(X, X) → Γ(U, V)`. -/
public theorem idealOnOpen_ideal_eq_map (U : S.U.toScheme.affineOpens) :
    (idealOnOpen S).ideal U =
      S.I.map ((S.U.ι.appLE ⊤ U.1 le_top).hom.comp
        (Scheme.ΓSpecIso (.of S.A)).inv.hom) := by
  have htop : (idealOnX S).ideal ⟨⊤, isAffineOpen_top S.X⟩ =
      S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom := by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  rw [idealOnOpen_eq_comap_idealOnX,
    Stacks.IdealSheaf.ideal_comap_appLE (idealOnX S) S.U.ι ⟨⊤, isAffineOpen_top S.X⟩ U le_top,
    htop, Ideal.map_map]

/-- The restriction to an affine open `V` of `U` of the global function on `U` determined by an
element of `Iⁿ` lies in the `n`-th power of the ideal of `I 𝒪_U` on `V`. -/
public theorem scalarMap_restrict_mem_idealOnOpen_pow (U : S.U.toScheme.affineOpens)
    (n : ℕ) {a : S.A} (ha : a ∈ S.I ^ n) :
    (S.U.toScheme.presheaf.map (homOfLE (le_top (a := U.1))).op).hom (scalarMap S a) ∈
      (idealOnOpen S).ideal U ^ n := by
  rw [idealOnOpen_ideal_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- **`H⁰(U, F_n)` is killed by the `(n+1)`-st power of `I`**, because `F_n` is: the sections of
`Iⁿ⁺¹F_n` vanish on every affine open, and the `F_n` are a sheaf. -/
public theorem idealPower_smul_globalSections_eq_zero (n : ℕ) {a : S.A}
    (ha : a ∈ S.I ^ (n + 1)) (y : (globalSectionsSystem S F).obj (op n)) :
    a • y = 0 := by
  change scalarMap S a • (show Γ(F.obj.obj (op n), ⊤) from y) = 0
  refine (F.obj.obj (op n)).isSheaf.section_ext (U := op (⊤ : S.U.toScheme.Opens))
    fun z _ => ?_
  obtain ⟨W, hW, hzW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := z) (U := (⊤ : S.U.toScheme.Opens)) trivial
  refine ⟨W, le_top, hzW, ?_⟩
  rw [map_zero]
  refine ((F.obj.obj (op n)).val.map_smul (homOfLE (le_top : W ≤ ⊤)).op
    (scalarMap S a) _).trans ?_
  exact smul_eq_zero_of_idealPowerMultiple_eq_bot (idealOnOpen S) (n + 1) (F.obj.obj (op n))
    (F.property.idealPowerMultiple_eq_bot n) ⟨W, hW⟩
    (scalarMap_restrict_mem_idealOnOpen_pow S ⟨W, hW⟩ (n + 1) ha) _

/-- A section of `Iⁿ⁺¹M` projects to zero in `H⁰(U, F_n)`, because `F_n` is killed by the
`(n+1)`-st power of the ideal. -/
public theorem limitProjection_kills_idealPower (n : ℕ) :
    S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F)) ≤
      LinearMap.ker (limit.π (globalSectionsSystem S F) (op n)).hom := by
  refine Submodule.smul_le.mpr fun a ha x _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  exact idealPower_smul_globalSections_eq_zero S F n ha _

/-- The quotient `M / Iⁿ⁺¹M` of the module `M = limₙ H⁰(U, F_n)` of compatible global
sections. -/
public abbrev quotientModule (n : ℕ) : ModuleCat.{u} S.A :=
  ModuleCat.of S.A (limitGlobalSections S F ⧸
    (S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F))))

/-- The canonical projection `M ⟶ M / Iⁿ⁺¹M`. -/
public abbrev quotientMap (n : ℕ) : limitGlobalSections S F ⟶ quotientModule S F n :=
  ModuleCat.ofHom (Submodule.mkQ _)

/-- The quasi-coherent sheaf `(M / Iⁿ⁺¹M)^~` on `X = Spec(A)`, restricted to the open
complement `U`. -/
public abbrev quotientSheaf (n : ℕ) : S.U.toScheme.Modules :=
  (Scheme.Modules.pullback S.U.ι).obj (tilde (quotientModule S F n))

/-- The projection `M / Iⁿ⁺¹M ⟶ H⁰(U, F_n)` induced by the `n`-th component of a compatible
system of sections. -/
public noncomputable def quotientProjection (n : ℕ) :
    quotientModule S F n ⟶ (globalSectionsSystem S F).obj (op n) :=
  ModuleCat.ofHom (X := quotientModule S F n) (Y := (globalSectionsSystem S F).obj (op n))
    (Submodule.liftQ (S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F)))
      ((limit.π (globalSectionsSystem S F) (op n)).hom :
        limitGlobalSections S F →ₗ[S.A] (globalSectionsSystem S F).obj (op n))
      (limitProjection_kills_idealPower S F n))

/-- The underlying morphism `(M / Iⁿ⁺¹M)^~|_U ⟶ F_n` of the canonical comparison map: the
transpose, along the two adjunctions, of `quotientProjection`. -/
@[irreducible] public noncomputable def canonicalComparisonMap (n : ℕ) :
    quotientSheaf S F n ⟶ F.obj.obj (op n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).homEquiv
      (tilde (quotientModule S F n)) (F.obj.obj (op n))).symm
    (((tilde.adjunction (R := CommRingCat.of S.A)).homEquiv (quotientModule S F n)
        ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj (op n)))).symm
      (quotientProjection S F n))

/-- The defining formula for `canonicalComparisonMap`, which is `irreducible`: it is the
transpose of `quotientProjection` along the two adjunctions. -/
public theorem canonicalComparisonMap_eq (n : ℕ) :
    canonicalComparisonMap S F n =
      ((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).homEquiv
          (tilde (quotientModule S F n)) (F.obj.obj (op n))).symm
        (((tilde.adjunction (R := CommRingCat.of S.A)).homEquiv (quotientModule S F n)
            ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj (op n)))).symm
          (quotientProjection S F n)) := by
  delta canonicalComparisonMap
  rfl

private theorem canonicalComparisonMap_homEquiv (n : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).homEquiv
        (tilde (quotientModule S F n)) (F.obj.obj (op n)))
          (canonicalComparisonMap S F n) =
      ((tilde.adjunction (R := CommRingCat.of S.A)).homEquiv (quotientModule S F n)
        ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj (op n)))).symm
          (quotientProjection S F n) := by
  rw [canonicalComparisonMap_eq]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).homEquiv
    (tilde (quotientModule S F n)) (F.obj.obj (op n))).apply_symm_apply _

/-- The image in `Γ((M / Iⁿ⁺¹M)^~|_U, ⊤)` of a compatible system of sections. -/
public noncomputable def limitSection (n : ℕ) (m : limitGlobalSections S F) :
    Γ(quotientSheaf S F n, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).unit.app
      (tilde (quotientModule S F n))).app ⊤)
    ((tilde.isoTop (R := CommRingCat.of S.A) (quotientModule S F n)).hom
      ((quotientMap S F n).hom m))

private theorem tilde_homEquiv_symm_app_top {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (N : (Spec R).Modules)
    (φ : M ⟶ moduleSpecΓFunctor.obj N) (m : M) :
    ((((tilde.adjunction (R := R)).homEquiv M N).symm φ).app ⊤)
      ((tilde.isoTop M).hom m) = φ.hom m := by
  have h := congrArg (fun α : M ⟶ moduleSpecΓFunctor.obj N => α.hom m)
    ((tilde.adjunction (R := R)).homEquiv_unit
      (f := ((tilde.adjunction (R := R)).homEquiv M N).symm φ))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private theorem canonicalComparisonMap_app_transpose (n : ℕ)
    (m : limitGlobalSections S F) :
    ((canonicalComparisonMap S F n).app ⊤) (limitSection S F n m) =
      ((((tilde.adjunction (R := CommRingCat.of S.A)).homEquiv (quotientModule S F n)
            ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj (op n)))).symm
          (quotientProjection S F n)).app ⊤)
        ((tilde.isoTop (R := CommRingCat.of S.A) (quotientModule S F n)).hom
          ((quotientMap S F n).hom m)) := by
  have hout := congrArg
    (fun α => (α.app ⊤).hom
      ((tilde.isoTop (R := CommRingCat.of S.A) (quotientModule S F n)).hom
        ((quotientMap S F n).hom m)))
    ((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).homEquiv_unit
      (f := canonicalComparisonMap S F n))
  rw [canonicalComparisonMap_homEquiv] at hout
  have h := hout.symm
  rw [Scheme.Modules.Hom.comp_app] at h
  change ((canonicalComparisonMap S F n).app ⊤)
    ((((Scheme.Modules.pullbackPushforwardAdjunction S.U.ι).unit.app
        (tilde (quotientModule S F n))).app ⊤)
      ((tilde.isoTop (R := CommRingCat.of S.A) (quotientModule S F n)).hom
        ((quotientMap S F n).hom m))) = _ at h
  exact h

private theorem canonicalComparisonMap_app_quotientProjection (n : ℕ)
    (m : limitGlobalSections S F) :
    ((canonicalComparisonMap S F n).app ⊤) (limitSection S F n m) =
      (quotientProjection S F n).hom ((quotientMap S F n).hom m) := by
  rw [canonicalComparisonMap_app_transpose]
  exact tilde_homEquiv_symm_app_top (quotientModule S F n)
    ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj (op n)))
    (quotientProjection S F n) ((quotientMap S F n).hom m)

/-- The canonical comparison map sends the section induced by `m ∈ M` to the `n`-th component
of `m`. -/
public theorem canonicalComparisonMap_app_limitSection (n : ℕ)
    (m : limitGlobalSections S F) :
    ((canonicalComparisonMap S F n).app ⊤) (limitSection S F n m) =
      (limit.π (globalSectionsSystem S F) (op n)).hom m :=
  (canonicalComparisonMap_app_quotientProjection S F n m).trans rfl

/-- The canonical comparison map `(M / Iⁿ⁺¹M)^~|_U ⟶ F_n`, characterized by sending the
section induced by `m ∈ M` to the `n`-th component of `m`. -/
public noncomputable def canonicalComparison (n : ℕ) :
    {f : quotientSheaf S F n ⟶ F.obj.obj (op n) //
      ∀ m : limitGlobalSections S F,
        (f.app ⊤) (limitSection S F n m) =
          (limit.π (globalSectionsSystem S F) (op n)).hom m} :=
  ⟨canonicalComparisonMap S F n, canonicalComparisonMap_app_limitSection S F n⟩

/-- A morphism out of a quasi-coherent module on a quasi-compact quasi-separated open of an
affine scheme is determined by its action on sections over the whole open. -/
public theorem hom_ext_of_app_top {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    {M N : X.Modules} [M.IsQuasicoherent] (f g : M ⟶ N)
    (h : f.app ⊤ = g.app ⊤) : f = g := by
  apply (Scheme.Modules.pushforward j).map_injective
  have : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := inferInstance
  apply (cancel_epi ((Scheme.Modules.pushforward j).obj M).fromTildeΓ).mp
  change (tilde.adjunction (R := R)).counit.app ((Scheme.Modules.pushforward j).obj M) ≫ _ =
    (tilde.adjunction (R := R)).counit.app ((Scheme.Modules.pushforward j).obj M) ≫ _
  have hmap : moduleSpecΓFunctor.map ((Scheme.Modules.pushforward j).map f) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward j).map g) := by
    ext x
    exact congrArg (fun t => t x) h
  rw [← (tilde.adjunction (R := R)).counit_naturality
      ((Scheme.Modules.pushforward j).map f),
    ← (tilde.adjunction (R := R)).counit_naturality
      ((Scheme.Modules.pushforward j).map g), hmap]

/-- **Stacks Project, Tag 0EHF.** If the inverse system `H⁰(U, F_n)` is Mittag-Leffler, every
canonical comparison map `(M / Iⁿ⁺¹M)^~|_U ⟶ F_n` is surjective. -/
@[stacks 0EHF]
public theorem epi_canonicalComparison_of_mittagLeffler
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F)) (n : ℕ) :
    Epi (canonicalComparison S F n).1 := by
  let := inverseSystem_moduleTower (globalSectionsSystem S F)
  obtain ⟨k, hnk, hrange⟩ :=
    exists_transition_range_eq_projection_range (globalSectionsSystem S F) hML n
  have hepi : Epi (F.obj.map (homOfLE hnk).op) := F.property.epi_map hnk
  have hqc : (F.obj.obj (op k)).IsQuasicoherent := F.property.isQuasicoherent k
  constructor
  intro N f g hfg
  apply (cancel_epi (F.obj.map (homOfLE hnk).op)).mp
  apply hom_ext_of_app_top S.U.ι
  ext x
  obtain ⟨m, hm⟩ := hrange ▸
    (show ((globalSectionsSystem S F).map (homOfLE hnk).op).hom x ∈
        Set.range (fun y =>
          ((globalSectionsSystem S F).map (homOfLE hnk).op).hom y) from ⟨x, rfl⟩)
  have heq := congrArg
    (fun q : quotientSheaf S F n ⟶ N => (q.app ⊤) (limitSection S F n m)) hfg
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply] at heq ⊢
  rw [(canonicalComparison S F n).property m] at heq
  exact (congrArg (fun y : (globalSectionsSystem S F).obj (op n) => (f.app ⊤) y)
    hm).symm.trans (heq.trans (congrArg
      (fun y : (globalSectionsSystem S F).obj (op n) => (g.app ⊤) y) hm))

end Surjectivity

private theorem exists_factor_through_limit_stage
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G)
    (P : ModuleCat.{u} A) (q : limit G ⟶ P) (i : ℕ)
    (hker : (limit.π G (op i)).hom.ker ≤ q.hom.ker) :
    ∃ (k : ℕ) (f : G.obj (op k) ⟶ P), limit.π G (op k) ≫ f = q := by
  obtain ⟨k, hik, hk⟩ := exists_transition_range_eq_projection_range G hML i
  let π := (limit.π G (op i)).hom
  let t := (G.map (homOfLE hik).op).hom
  let r : G.obj (op k) →ₗ[A] π.range := t.codRestrict π.range (fun x => hk.le ⟨x, rfl⟩)
  let f : G.obj (op k) →ₗ[A] P :=
    (π.ker.liftQ q.hom hker) ∘ₗ π.quotKerEquivRange.symm.toLinearMap ∘ₗ r
  refine ⟨k, ModuleCat.ofHom f, ?_⟩
  ext m
  have hm : t ((limit.π G (op k)).hom m) = π m :=
    ConcreteCategory.congr_hom (limit.w G (homOfLE hik).op) m
  have hr : r ((limit.π G (op k)).hom m) = π.rangeRestrict m := Subtype.ext hm
  change (π.ker.liftQ q.hom hker)
    (π.quotKerEquivRange.symm (r ((limit.π G (op k)).hom m))) = q.hom m
  rw [hr]
  change (π.ker.liftQ q.hom hker)
    (π.quotKerEquivRange.symm ⟨π m, _⟩) = q.hom m
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

private theorem limit_cone_detects_eventual_equality
    {A : Type u} [CommRing A] (G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [InverseSystem (fun _ _ h => (G.map (homOfLE h).op).hom)]
    (hML : IsMittagLefflerCategorical G)
    (i j : ℕᵒᵖ) (Y : ModuleCat.{u} A) (f : G.obj i ⟶ Y) (g : G.obj j ⟶ Y)
    (h : limit.π G i ≫ f = limit.π G j ≫ g) :
    ∃ (k : ℕᵒᵖ) (a : k ⟶ i) (b : k ⟶ j), G.map a ≫ f = G.map b ≫ g := by
  let n := max i.unop j.unop
  let ai : op n ⟶ i := (homOfLE (Nat.le_max_left _ _)).op
  let aj : op n ⟶ j := (homOfLE (Nat.le_max_right _ _)).op
  obtain ⟨k, hnk, hk⟩ := exists_transition_range_eq_projection_range G hML n
  let a : op k ⟶ op n := (homOfLE hnk).op
  refine ⟨op k, a ≫ ai, a ≫ aj, ?_⟩
  ext x
  obtain ⟨m, hm⟩ : ∃ m, (limit.π G (op n)).hom m = (G.map a).hom x := hk.le ⟨x, rfl⟩
  have hi := ConcreteCategory.congr_hom (limit.w G ai) m
  have hj := ConcreteCategory.congr_hom (limit.w G aj) m
  have hm' := ConcreteCategory.congr_hom h m
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  change f.hom ((G.map ai).hom ((G.map a).hom x)) =
    g.hom ((G.map aj).hom ((G.map a).hom x))
  rw [← hm]
  change (G.map ai).hom ((limit.π G (op n)).hom m) = (limit.π G i).hom m at hi
  change (G.map aj).hom ((limit.π G (op n)).hom m) = (limit.π G j).hom m at hj
  rw [hi, hj]
  exact hm'

/-- The submodules `Iᵏ M` form a basis of neighbourhoods of `0` for the `I`-adic module
topology. -/
private theorem hasBasis_nhds_zero_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    (@nhds M (I.adicModuleTopology M) 0).HasBasis (fun _ : ℕ => True)
      (fun k => ((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
  let : TopologicalSpace R := I.adicTopology
  refine ⟨fun U => ?_⟩
  rw [(I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis M)).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨V, ⟨k, rfl⟩, hVU⟩
    exact ⟨k, trivial, hVU⟩
  · rintro ⟨k, -, hVU⟩
    exact ⟨((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M), ⟨k, rfl⟩, hVU⟩

/-- **The content of the topology hypothesis.** If the limit topology on `M` agrees with its
`I`-adic topology, then every `I`-adic neighbourhood of `0` contains the kernel of some
projection `M → H⁰(U, F_k)`; equivalently `(M_n)` and `(M/IⁿM)` are pro-isomorphic. -/
public theorem exists_projection_ker_le_adicPower
    (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : Stacks.Algebraization.limitGlobalSections S F =>
        (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (Stacks.Algebraization.limitGlobalSections S F))
    (n : ℕ) :
    ∃ k : ℕ, LinearMap.ker
      (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op k)).hom ≤
        S.I ^ (n + 1) • (⊤ : Submodule S.A (Stacks.Algebraization.limitGlobalSections S F)) := by
  let M := (Stacks.Algebraization.limitGlobalSections S F : Type u)
  let : AddCommGroup M := (Stacks.Algebraization.limitGlobalSections S F).isAddCommGroup
  let : Module S.A M := (Stacks.Algebraization.limitGlobalSections S F).isModule
  let G := Stacks.Algebraization.globalSectionsSystem S F
  let π (k : ℕ) : M →ₗ[S.A] G.obj (op k) := (limit.π G (op k)).hom
  have hB := hasBasis_nhds_zero_adicModuleTopology S.I M
  let T : TopologicalSpace M := ⨅ k : ℕ,
    TopologicalSpace.induced (π k) (⊥ : TopologicalSpace (G.obj (op k)))
  have hmem :
      ((S.I ^ (n + 1) • (⊤ : Submodule S.A M) : Submodule S.A M) : Set M) ∈
        @nhds M T 0 := by
    change ((S.I ^ (n + 1) • (⊤ : Submodule S.A M) : Submodule S.A M) : Set M) ∈
      @nhds M (⨅ k : ℕ, TopologicalSpace.induced (π k)
        (⊥ : TopologicalSpace (G.obj (op k)))) 0
    rw [htop]
    exact hB.mem_of_mem (i := n + 1) trivial
  rw [nhds_iInf] at hmem
  obtain ⟨J, hJfin, V, hV, hVeq⟩ := (Filter.mem_iInf).1 hmem
  obtain ⟨k, hk⟩ := hJfin.bddAbove
  refine ⟨k, ?_⟩
  intro x hx
  change x ∈ ((S.I ^ (n + 1) • (⊤ : Submodule S.A M) : Submodule S.A M) : Set M)
  rw [hVeq, Set.mem_iInter]
  intro j
  have hj : (j : ℕ) ≤ k := hk j.2
  let : TopologicalSpace (G.obj (op j.1)) := ⊥
  have hVj : V j ∈ @nhds M
      (TopologicalSpace.induced (π j.1) (⊥ : TopologicalSpace (G.obj (op j.1)))) 0 := hV j
  have hproj := congrArg
    (fun f : Stacks.Algebraization.limitGlobalSections S F ⟶ G.obj (op j.1) => f.hom x)
    (limit.w G ((homOfLE hj).op))
  have hxj : (π j.1) x = 0 := by
    have hxk : (π k) x = 0 := LinearMap.mem_ker.mp hx
    change ((G.map (homOfLE hj).op).hom ((π k) x)) = (π j.1) x at hproj
    rw [hxk] at hproj
    simpa using hproj.symm
  obtain ⟨U, hU, hUV⟩ :=
    (mem_nhds_induced (π j.1) (0 : M) (V j)).mp hVj
  have hzero : (π j.1) 0 ∈ U := mem_of_mem_nhds hU
  have hxpre : x ∈ (π j.1) ⁻¹' U := by
    change (π j.1) x ∈ U
    rw [hxj]
    simpa using hzero
  exact hUV hxpre

private theorem finite_limitQuotient
    (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : Stacks.Algebraization.limitGlobalSections S F =>
        (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (Stacks.Algebraization.limitGlobalSections S F))
    (hfinite : ∀ n : ℕ, Module.Finite S.A
      (LinearMap.range (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom))
    (n : ℕ) :
    Module.Finite S.A
      ((Stacks.Algebraization.limitGlobalSections S F : Type u) ⧸
        S.I ^ (n + 1) • (⊤ : Submodule S.A (Stacks.Algebraization.limitGlobalSections S F))) := by
  let M := (Stacks.Algebraization.limitGlobalSections S F : Type u)
  let : AddCommGroup M := (Stacks.Algebraization.limitGlobalSections S F).isAddCommGroup
  let : Module S.A M := (Stacks.Algebraization.limitGlobalSections S F).isModule
  let G := Stacks.Algebraization.globalSectionsSystem S F
  let π (k : ℕ) : M →ₗ[S.A] G.obj (op k) := (limit.π G (op k)).hom
  let N : Submodule S.A M := S.I ^ (n + 1) • (⊤ : Submodule S.A M)
  obtain ⟨k, hker⟩ := exists_projection_ker_le_adicPower S F htop n
  have hfiniteKer : Module.Finite S.A (M ⧸ LinearMap.ker (π k)) := by
    rw [Module.Finite.equiv_iff (π k).quotKerEquivRange]
    exact hfinite k
  let f : M ⧸ LinearMap.ker (π k) →ₗ[S.A] M ⧸ N :=
    (LinearMap.ker (π k)).liftQ (N.mkQ) (by rwa [Submodule.ker_mkQ])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    refine ⟨(LinearMap.ker (π k)).mkQ x, ?_⟩
    simp [f, Submodule.liftQ_apply]
  exact Module.Finite.of_surjective f hsurj

private theorem exists_adicPower_le_projectionKer
    (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : Stacks.Algebraization.limitGlobalSections S F =>
        (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (Stacks.Algebraization.limitGlobalSections S F))
    (k : ℕ) :
    ∃ n : ℕ, S.I ^ n • (⊤ : Submodule S.A (Stacks.Algebraization.limitGlobalSections S F)) ≤
      LinearMap.ker (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op k)).hom := by
  let M := (Stacks.Algebraization.limitGlobalSections S F : Type u)
  let : AddCommGroup M := (Stacks.Algebraization.limitGlobalSections S F).isAddCommGroup
  let : Module S.A M := (Stacks.Algebraization.limitGlobalSections S F).isModule
  let G := Stacks.Algebraization.globalSectionsSystem S F
  let π (j : ℕ) : M →ₗ[S.A] G.obj (op j) := (limit.π G (op j)).hom
  have hB := hasBasis_nhds_zero_adicModuleTopology S.I M
  have hker :
      ((LinearMap.ker (π k) : Submodule S.A M) : Set M) ∈
        @nhds M (TopologicalSpace.induced (π k) (⊥ : TopologicalSpace (G.obj (op k))) ) 0 := by
    let : TopologicalSpace M :=
      TopologicalSpace.induced (π k) (⊥ : TopologicalSpace (G.obj (op k)))
    let : TopologicalSpace (G.obj (op k)) := ⊥
    let : DiscreteTopology (G.obj (op k)) := discreteTopology_bot _
    have hset : (LinearMap.ker (π k) : Set M) = (π k) ⁻¹' ({0} : Set (G.obj (op k))) := by
      ext x
      simp [LinearMap.mem_ker]
    have hopen : IsOpen (LinearMap.ker (π k) : Set M) := by
      rw [hset]
      exact isOpen_induced_iff.mpr ⟨{0}, isOpen_discrete _, rfl⟩
    exact hopen.mem_nhds (by simp)
  have hkerT :
      ((LinearMap.ker (π k) : Submodule S.A M) : Set M) ∈
        @nhds M (⨅ j : ℕ,
          TopologicalSpace.induced (π j) (⊥ : TopologicalSpace (G.obj (op j)))) 0 := by
    rw [nhds_iInf]
    exact Filter.mem_iInf_of_mem k hker
  have hkerAdic :
      ((LinearMap.ker (π k) : Submodule S.A M) : Set M) ∈
        @nhds M (S.I.adicModuleTopology M) 0 := by
    rwa [htop] at hkerT
  obtain ⟨n, -, hsub⟩ := hB.mem_iff.mp hkerAdic
  exact ⟨n, fun _ hx => hsub hx⟩

private theorem finite_completion {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I.FG) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
  let B := AdicCompletion I R
  let N := AdicCompletion I M
  let J : Ideal B := I.map (algebraMap R B)
  let P : Submodule B N := J • ⊤
  have hP : P.restrictScalars R = I • (⊤ : Submodule R N) := by
    simpa [P, J] using Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule B N)
  have hq : Module.Finite R (N ⧸ P.restrictScalars R) := by
    rw [hP]
    have e := AdicCompletion.quotPowSMulTopEquiv hI M 1
    rw [show I ^ 1 = I from _root_.pow_one I] at e
    exact (Module.Finite.equiv_iff e).mpr inferInstance
  have : Module.Finite R (N ⧸ P) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv R P)
  have : Module.Finite B (N ⧸ P) :=
    Module.Finite.of_restrictScalars_finite R B (N ⧸ P)
  have hqJ : Module.Finite (B ⧸ J) (N ⧸ J • (⊤ : Submodule B N)) :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ J) _
  have : IsAdicComplete J B :=
    (IsAdicComplete.map_algebraMap_iff I B).mpr (AdicCompletion.isAdicComplete hI)
  have : IsAdicComplete J N :=
    (IsAdicComplete.map_algebraMap_iff I N).mpr (AdicCompletion.isAdicComplete hI)
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    J (IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff J N)) hqJ

private theorem completion_projection_comp_of
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : AdicCompletion I M →ₗ[R] P) (n : ℕ)
    (hf : Function.Surjective f)
    (hker : f.ker = I ^ n • (⊤ : Submodule R (AdicCompletion I M))) :
    Function.Surjective (f ∘ₗ AdicCompletion.of I M) ∧
      (f ∘ₗ AdicCompletion.of I M).ker = I ^ n • (⊤ : Submodule R M) := by
  have hker' : f.ker = (AdicCompletion.eval I M n).ker :=
    hker.trans (AdicCompletion.pow_smul_top_eq_ker_eval hI)
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨m, hm⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective
      (AdicCompletion.eval I M n x)
    refine ⟨m, ?_⟩
    change f (AdicCompletion.of I M m) = f x
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LinearMap.mem_ker.mp
    rw [hker']
    change AdicCompletion.eval I M n (AdicCompletion.of I M m - x) = 0
    rw [map_sub, AdicCompletion.eval_of, hm, sub_self]
  · ext m
    rw [LinearMap.mem_ker]
    change f (AdicCompletion.of I M m) = 0 ↔ m ∈ I ^ n • (⊤ : Submodule R M)
    rw [← LinearMap.mem_ker, hker', LinearMap.mem_ker, AdicCompletion.eval_of]
    change m ∈ (I ^ n • (⊤ : Submodule R M)).mkQ.ker ↔ _
    rw [Submodule.ker_mkQ]

private theorem finite_quotient_changeScalars
    {R T : Type u} [CommRing R] [CommRing T] (e : R ≃+* T)
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    letI : Module T M := Module.compHom M e.symm.toRingHom
    Module.Finite T (M ⧸ (I.map e.toRingHom) • (⊤ : Submodule T M)) := by
  let : Algebra R T := e.toRingHom.toAlgebra
  let : Module T M := Module.compHom M e.symm.toRingHom
  have : IsScalarTower R T M := ⟨by
    intro r t m
    change e.symm (e r * t) • m = r • e.symm t • m
    simp [mul_smul]⟩
  let P : Submodule T M := I.map e.toRingHom • ⊤
  have hP : P.restrictScalars R = I • (⊤ : Submodule R M) :=
    (Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule T M)).trans
      (by rw [Submodule.restrictScalars_top])
  have : Module.Finite R (M ⧸ P.restrictScalars R) := by
    rw [hP]
    infer_instance
  have : Module.Finite R (M ⧸ P) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv R P)
  exact Module.Finite.of_restrictScalars_finite R T _

private theorem exists_coherentSystem_from_finite_completion
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) (N : FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤))) :
    ∃ G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I),
      ∃ e : (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
        (AdicCompletion I Γ(X, ⊤)))).obj N.obj ≅
        limit (Stacks.Coherent.globalSectionsSystem G),
      ∀ n : ℕ, Function.Surjective ((e.hom ≫
          limit.π (Stacks.Coherent.globalSectionsSystem G) (op n)).hom) ∧
        LinearMap.ker ((e.hom ≫
          limit.π (Stacks.Coherent.globalSectionsSystem G) (op n)).hom) =
          I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤)
            ((ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
              (AdicCompletion I Γ(X, ⊤)))).obj N.obj)) := by
  let E := Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I
  let G := E.inverse.obj N
  let η := (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
      (AdicCompletion I Γ(X, ⊤)))).mapIso
      ((ObjectProperty.ι _).mapIso (E.counitIso.app N).symm)
  let e := η ≪≫ Stacks.Coherent.globalSectionsComparison X I G
  refine ⟨G, e, fun n => ⟨?_, ?_⟩⟩
  · exact (Stacks.Coherent.globalSectionsComparison_projection_surjective X I G n).comp
      η.toLinearEquiv.surjective
  · change LinearMap.ker (((Stacks.Coherent.globalSectionsComparison X I G).hom ≫
        limit.π (Stacks.Coherent.globalSectionsSystem G) (op n)).hom ∘ₗ η.hom.hom) = _
    rw [LinearMap.ker_comp,
      Stacks.Coherent.globalSectionsComparison_projection_ker X I G n,
      ← Iso.toLinearMap_toLinearEquiv η,
      Submodule.comap_smul'' η.toLinearEquiv.injective
        (by rw [LinearMap.range_eq_top.mpr η.toLinearEquiv.surjective]),
      Submodule.comap_top]
private theorem exists_coherentSystem_of_finite_quotient
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) (M : ModuleCat.{u} Γ(X, ⊤))
    [Module.Finite Γ(X, ⊤) (M ⧸ I • (⊤ : Submodule Γ(X, ⊤) M))] :
    ∃ G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I),
      ∃ p : (Functor.const ℕᵒᵖ).obj M ⟶ Stacks.Coherent.globalSectionsSystem G,
      ∀ n : ℕ, Function.Surjective (p.app (op n)).hom ∧
        LinearMap.ker (p.app (op n)).hom =
          I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤) M) := by
  have hI : I.FG := IsNoetherian.noetherian I
  have : Module.Finite (AdicCompletion I Γ(X, ⊤)) (AdicCompletion I M) :=
    finite_completion I hI M
  obtain ⟨G, e, he⟩ := exists_coherentSystem_from_finite_completion X I
    (FGModuleCat.of (AdicCompletion I Γ(X, ⊤)) (AdicCompletion I M))
  let q : M ⟶ limit (Stacks.Coherent.globalSectionsSystem G) :=
    ModuleCat.ofHom (AdicCompletion.of I M) ≫ e.hom
  let p : (Functor.const ℕᵒᵖ).obj M ⟶ Stacks.Coherent.globalSectionsSystem G := {
    app j := q ≫ limit.π (Stacks.Coherent.globalSectionsSystem G) j
    naturality i j f := by simp [limit.w]
  }
  exact ⟨G, p, fun n => completion_projection_comp_of I hI M
    ((e.hom ≫ limit.π (Stacks.Coherent.globalSectionsSystem G) (op n)).hom)
    (n + 1) (he n).1 (he n).2⟩

private theorem exists_factor_of_surjective
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A}
    (f : M ⟶ N) (hf : Function.Surjective f.hom) (g : M ⟶ P)
    (hker : f.hom.ker ≤ g.hom.ker) : ∃ h : N ⟶ P, f ≫ h = g := by
  let h := (f.hom.ker.liftQ g.hom hker) ∘ₗ
    (f.hom.quotKerEquivOfSurjective hf).symm.toLinearMap
  refine ⟨ModuleCat.ofHom h, ?_⟩
  ext x
  change (f.hom.ker.liftQ g.hom hker)
    ((f.hom.quotKerEquivOfSurjective hf).symm (f.hom x)) = g.hom x
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The Mittag-Leffler, topology, and finite-image hypotheses imply canonical
extension of a coherent adic system to `X`. -/
@[stacks 0EHH "canonical extension"]
public theorem canonicallyExtends_of_finite_limit_images
    (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S))
    (hML : IsMittagLefflerCategorical (Stacks.Algebraization.globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : Stacks.Algebraization.limitGlobalSections S F =>
        (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (Stacks.Algebraization.limitGlobalSections S F))
    (hfinite : ∀ n : ℕ, Module.Finite S.A
      (LinearMap.range (limit.π (Stacks.Algebraization.globalSectionsSystem S F) (op n)).hom)) :
    Stacks.Algebraization.CanonicallyExtends S F := by
  let M := Stacks.Algebraization.limitGlobalSections S F
  let R := Γ(S.X, ⊤)
  let e : S.A ≃+* R :=
    (Scheme.ΓSpecIso (.of S.A)).commRingCatIsoToRingEquiv.symm
  have hfin : Module.Finite S.A (M ⧸ S.I • (⊤ : Submodule S.A M)) := by
    have h := finite_limitQuotient S F htop hfinite 0
    rwa [Nat.zero_add, pow_one] at h
  let : Module R M := Module.compHom M e.symm.toRingHom
  have : Module.Finite R (M ⧸ S.I.map e.toRingHom • (⊤ : Submodule R M)) :=
    finite_quotient_changeScalars e S.I M
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S.A e
  obtain ⟨G, p, hp⟩ := exists_coherentSystem_of_finite_quotient S.X
    (S.I.map e.toRingHom) (ModuleCat.of R M)
  let H := Stacks.Algebraization.globalSectionsSystem S F
  let Q := Stacks.Coherent.globalSectionsSystem G ⋙ ModuleCat.restrictScalars e.toRingHom
  let q : (Functor.const ℕᵒᵖ).obj M ⟶ Q := {
    app j := ModuleCat.ofHom (X := M) (Y := Q.obj j) {
      toFun := fun x => (p.app j).hom x
      map_add' x y := (p.app j).hom.map_add x y
      map_smul' r x := by
        change (p.app j).hom (r • x) = e r • (p.app j).hom x
        have h := (p.app j).hom.map_smul (e r) x
        change (p.app j).hom (e.symm (e r) • x) = e r • (p.app j).hom x at h
        rwa [e.symm_apply_apply] at h
    }
    naturality i j f := by
      ext x
      exact ConcreteCategory.congr_hom (p.naturality f) x
  }
  let : Algebra S.A R := e.toRingHom.toAlgebra
  have : IsScalarTower S.A R M := ⟨by
    intro r t m
    change e.symm (e r * t) • m = r • e.symm t • m
    simp [mul_smul]⟩
  have hq (n : ℕ) : Function.Surjective (q.app (op n)).hom ∧
      (q.app (op n)).hom.ker = S.I ^ (n + 1) • (⊤ : Submodule S.A M) := by
    refine ⟨(hp n).1, ?_⟩
    have hk := congrArg (fun N : Submodule R M => N.restrictScalars S.A) (hp n).2
    rw [← Ideal.map_pow] at hk
    have ht := Submodule.restrictScalars_map_smul_eq (S.I ^ (n + 1))
      (⊤ : Submodule R M)
    rw [Submodule.restrictScalars_top] at ht
    exact hk.trans ht
  let c : Cone H := limit.cone H
  let d : Cone Q := ⟨M, q⟩
  let := inverseSystem_moduleTower H
  have hdc : ∀ j, ∃ i, ∃ f : H.obj i ⟶ Q.obj j,
      c.π.app i ≫ f = (Iso.refl M).hom ≫ d.π.app j := by
    intro j
    obtain ⟨i, hi⟩ := exists_projection_ker_le_adicPower S F htop j.unop
    obtain ⟨k, f, hf⟩ := exists_factor_through_limit_stage H hML (Q.obj j)
      (q.app j) i (by rwa [(hq j.unop).2])
    exact ⟨op k, f, by simpa [c, d] using hf⟩
  have hcd : ∀ i, ∃ j, ∃ f : Q.obj j ⟶ H.obj i,
      d.π.app j ≫ f = (Iso.refl M).inv ≫ c.π.app i := by
    intro i
    obtain ⟨n, hn⟩ := exists_adicPower_le_projectionKer S F htop i.unop
    obtain ⟨f, hf⟩ := exists_factor_of_surjective (q.app (op n)) (hq n).1
      (limit.π H i) (by
        rw [(hq n).2]
        exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))).trans hn)
    exact ⟨op n, f, by simpa [c, d] using hf⟩
  have hc : ∀ (i j : ℕᵒᵖ) (Y : ModuleCat.{u} S.A)
      (f : H.obj i ⟶ Y) (g : H.obj j ⟶ Y),
      c.π.app i ≫ f = c.π.app j ≫ g →
      ∃ (k : ℕᵒᵖ) (a : k ⟶ i) (b : k ⟶ j), H.map a ≫ f = H.map b ≫ g := by
    exact limit_cone_detects_eventual_equality H hML
  have hd : ∀ (i j : ℕᵒᵖ) (Y : ModuleCat.{u} S.A)
      (f : Q.obj i ⟶ Y) (g : Q.obj j ⟶ Y),
      d.π.app i ≫ f = d.π.app j ≫ g →
      ∃ (k : ℕᵒᵖ) (a : k ⟶ i) (b : k ⟶ j), Q.map a ≫ f = Q.map b ≫ g :=
    cone_detects_eventual_equality_of_epi d
      (fun i => (ModuleCat.epi_iff_surjective _).mpr (hq i.unop).1)
  let E := tildeEquiv (R := CommRingCat.of S.A)
  let D := Stacks.Coherent.quasicoherentDiagram G
  have hQ : Q = D ⋙ E.inverse := rfl
  let t : Q ⋙ E.functor ≅ D :=
    Functor.isoWhiskerRight (eqToIso hQ) E.functor ≪≫
      Functor.associator D E.inverse E.functor ≪≫
      Functor.isoWhiskerLeft D E.counitIso ≪≫ Functor.rightUnitor D
  let z := colimitYonedaIsoOfMappedCones E c d (Iso.refl M) hc hd hcd hdc
  have z' : colimit ((Q ⋙ E.functor).op ⋙ yoneda) ≅ colimit (D.op ⋙ yoneda) :=
    HasColimit.isoOfNatIso (Functor.isoWhiskerRight (NatIso.op t.symm) yoneda)
  exact ⟨G, diagramToPro_iso_of_colimitYonedaIso
    (Stacks.Algebraization.tildeGlobalSectionsSystem S F) D (z ≪≫ z')⟩

end Stacks.Algebraization

end

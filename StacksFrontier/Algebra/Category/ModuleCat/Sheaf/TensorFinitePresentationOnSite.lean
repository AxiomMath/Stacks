module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Finite presentation on a site of a tensor product of sheaves of modules

Stacks 03L6 says that the tensor product of two sheaves of modules of finite presentation on a
ringed site is of finite presentation. This file proves it for the covering-family rendering
`SheafOfModules.IsFinitePresentationOnSite` of Stacks 03DL(7), on an arbitrary ringed site, with
no size hypothesis relating the universe of the objects of the site to that of its structure
sheaf.

## Main results

* `Stacks.SheafOfModules.hasSectionsPresentation_of_sectionwiseEquiv` and
  `Stacks.SheafOfModules.isFinitePresentationOnSite_of_sectionwiseEquiv`: section-level
  presentation data, and hence finite presentation on the site, transport along a sectionwise
  additive equivalence semilinear over a sectionwise ring equivalence.
* `Stacks.SheafOfModules.CoherentLift.isFinitePresentationOnSite_liftModule_iff`: finite
  presentation is unchanged by the universe lift `Stacks.SheafOfModules.CoherentLift.liftModule`.
* `SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation'`: Mathlib's finite
  presentation implies finite presentation on the site, in any module universe at which the
  sheafification on the slices of the site needed to state the former exists.
* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite`:
  **Stacks 03L6, finite presentation, on an arbitrary ringed site.**

## Implementation notes

`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentation` proves the same
statement for Mathlib's `SheafOfModules.IsFinitePresentation`, under `UnivLE.{max v u, w}`, which
fails on the big sites of algebraic stacks (objects one universe above the structure sheaf). The
route here is the one `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherentOnSite`
takes for coherence: lift the sections of the structure sheaf and of the modules to the universe
`max u v w` by `Stacks.SheafOfModules.CoherentLift.liftModule`, where the size hypothesis holds,
apply the Mathlib-predicate statement there, and come back along
`Stacks.SheafOfModules.CoherentLift.tensorLiftIso`. The two crossings between the predicates are
`SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` and
`SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation'`, and the crossing of the lift
is read on sections, through `Stacks.SheafOfModules.HasSectionsPresentation`, which is stated
purely in terms of sections and coefficients and so transports along `ULift` with every
compatibility holding by `rfl`.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace Stacks.SheafOfModules

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} {S : Sheaf J RingCat.{w'}}
  {M : _root_.SheafOfModules.{w} R} {N : _root_.SheafOfModules.{w'} S}
  (eR : ∀ V, R.obj.obj V ≃+* S.obj.obj V)
  (hR : ∀ {V W} (f : V ⟶ W) (a : R.obj.obj V), eR W (R.obj.map f a) = S.obj.map f (eR V a))
  (e : ∀ V, M.val.obj V ≃+ N.val.obj V)
  (he : ∀ V (a : R.obj.obj V) (x : M.val.obj V), e V (a • x) = eR V a • e V x)
  (hn : ∀ {V W} (f : V ⟶ W) (x : M.val.obj V),
    e W (M.val.restrictₛₗ f x) = N.val.restrictₛₗ f (e V x))

include he in
private theorem sectionwiseEquiv_sum_smul {V : Cᵒᵖ} {n : ℕ} (a : Fin n → R.obj.obj V)
    (x : Fin n → M.val.obj V) : e V (∑ i, a i • x i) = ∑ i, eR V (a i) • e V (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => he V (a i) (x i)

include hR he hn in
/-- **Section-level presentation data transports along a sectionwise equivalence.** -/
theorem hasSectionsPresentation_of_sectionwiseEquiv {Z : C}
    (h : HasSectionsPresentation J M Z) : HasSectionsPresentation J N Z := by
  obtain ⟨n, p, s, r, hr, hs, hrel⟩ := h
  refine ⟨n, p, fun i => e _ (s i), fun k i => eR _ (r k i), fun k => ?_, ?_, ?_⟩
  · rw [← sectionwiseEquiv_sum_smul eR e he, hr k, map_zero]
  · intro V f t
    obtain ⟨T, hT, hc⟩ := hs V f ((e _).symm t)
    refine ⟨T, hT, fun W g hg => ?_⟩
    obtain ⟨a, ha⟩ := hc W g hg
    refine ⟨fun i => eR _ (a i), ?_⟩
    have h1 := congrArg (e _) ha
    rw [sectionwiseEquiv_sum_smul eR e he, hn, AddEquiv.apply_symm_apply] at h1
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    rw [hn]
  · intro V hV τ hτ
    have hτ' : ∑ i, (eR _).symm (τ i) • M.val.restrictₛₗ hV.op (s i) = 0 := by
      apply (e _).injective
      rw [sectionwiseEquiv_sum_smul eR e he, map_zero]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hτ
      rw [RingEquiv.apply_symm_apply, hn]
    obtain ⟨T, hT, hd⟩ := hrel V hV _ hτ'
    refine ⟨T, hT, fun B g hg => ?_⟩
    obtain ⟨d, hd⟩ := hd g hg
    refine ⟨fun k => eR _ (d k), fun i => ?_⟩
    have h1 := congrArg (eR _) (hd i)
    rw [map_sum, hR, RingEquiv.apply_symm_apply] at h1
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
    rw [map_mul, hR]

include hR he hn in
/-- **Finite presentation on a site transports along a sectionwise equivalence.** -/
theorem isFinitePresentationOnSite_of_sectionwiseEquiv (h : M.IsFinitePresentationOnSite) :
    N.IsFinitePresentationOnSite := by
  constructor
  intro U
  obtain ⟨I, V, f, hcov, hpres⟩ := h.locally_hasFiniteGlobalPresentation U
  exact ⟨I, V, f, hcov, fun i => hasFiniteGlobalPresentation_over_of_hasSectionsPresentation
    (hasSectionsPresentation_of_sectionwiseEquiv eR hR e he hn
      (hasSectionsPresentation_of_hasFiniteGlobalPresentation M (V i) (hpres i)))⟩

end Transport

namespace CoherentLift

/-- **Finite presentation is unchanged by the sectionwise `ULift` of a sheaf of modules and of
its structure sheaf.** -/
theorem isFinitePresentationOnSite_liftModule_iff (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (liftModule.{u, v, w} X M).IsFinitePresentationOnSite ↔ M.IsFinitePresentationOnSite :=
  ⟨isFinitePresentationOnSite_of_sectionwiseEquiv (fun _ ↦ ULift.ringEquiv) (fun _ _ ↦ rfl)
      (fun _ ↦ AddEquiv.ulift) (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl),
    isFinitePresentationOnSite_of_sectionwiseEquiv (fun _ ↦ ULift.ringEquiv.symm)
      (fun _ _ ↦ rfl) (fun _ ↦ AddEquiv.ulift.symm) (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)⟩

end CoherentLift

end Stacks.SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Mathlib's finite presentation implies finite presentation on the site.** The finitely
presented members of a quasi-coherent datum cover the final object, and a finite global
presentation over one of them restricts along any arrow into it. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation'
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) [M.IsFinitePresentation] : M.IsFinitePresentationOnSite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hpres : ∀ i, (M.over (q.X i)).HasFiniteGlobalPresentation := fun i =>
    HasFiniteGlobalPresentation.of_presentation' (q.presentation i) (hq.isFinite_presentation i)
  refine ⟨fun W => ?_⟩
  refine ⟨{g : Over W // (Sieve.ofObjects q.X W) g.hom}, fun a => a.1.left, fun a => a.1.hom,
    ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {g : Over W // (Sieve.ofObjects q.X W) g.hom} => a.1.left)
        (fun a => a.1.hom) = Sieve.ofObjects q.X W := by
      refine le_antisymm (fun X g hg => ?_) (fun X g hg => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact (Sieve.ofObjects q.X W).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 X, by simp⟩
    rw [hEq]
    exact q.coversTop W
  · intro a
    obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff q.X a.1.hom).mp a.2
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M b (hpres k)

end SheafOfModules

namespace Stacks.SheafOfModules.TensorLocalProperties

open CoherentLift

/-- **Stacks Project, Tag 03L6, finite presentation case, on an arbitrary ringed site.** The
tensor product of two sheaves of modules of finite presentation on a ringed site, in the sense
of Stacks 03DL(7), is of finite presentation.

No size hypothesis relates the objects of the site to its structure sheaf: the statement is
proved at the universe lift of the ringed site, where
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentation` applies, and
transported back along `Stacks.SheafOfModules.CoherentLift.tensorLiftIso` and
`Stacks.SheafOfModules.CoherentLift.isFinitePresentationOnSite_liftModule_iff`. -/
theorem tensorSheaf_isFinitePresentationOnSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFinitePresentationOnSite) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G).IsFinitePresentationOnSite := by
  let i1 : HasSheafify (liftRingedSite.{u, v, w} X).J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u}
      (liftRingedSite.{u, v, w} X).J
  let i2 : (liftRingedSite.{u, v, w} X).J.WEqualsLocallyBijective
      AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v}
      (liftRingedSite.{u, v, w} X).J
  let i3 : ∀ U : (liftRingedSite.{u, v, w} X).C,
      HasSheafify ((liftRingedSite.{u, v, w} X).J.over U) AddCommGrpCat.{max u v w} := fun U ↦
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v}
      ((liftRingedSite.{u, v, w} X).J.over U)
  let i4 : ∀ U : (liftRingedSite.{u, v, w} X).C,
      ((liftRingedSite.{u, v, w} X).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{max u v w} := fun U ↦
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} ((liftRingedSite.{u, v, w} X).J.over U)
  have hFl : (liftModule.{u, v, w} X F).IsFinitePresentation :=
    _root_.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
      ((isFinitePresentationOnSite_liftModule_iff X F).2 hF)
  have hGl : (liftModule.{u, v, w} X G).IsFinitePresentation :=
    _root_.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
      ((isFinitePresentationOnSite_liftModule_iff X G).2 hG)
  have ht := tensorSheaf_isFinitePresentation (liftRingedSite.{u, v, w} X)
    (liftModule.{u, v, w} X F) (liftModule.{u, v, w} X G)
  have ht' := _root_.SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation'
    (((Stacks.SheafOfModules.Tensor.sheafTensor (liftRingedSite.{u, v, w} X).O).obj
      (liftModule.{u, v, w} X F)).obj (liftModule.{u, v, w} X G))
  exact (isFinitePresentationOnSite_liftModule_iff X _).1
    (_root_.SheafOfModules.IsFinitePresentationOnSite.of_iso (tensorLiftIso X F G) ht')

end Stacks.SheafOfModules.TensorLocalProperties

end

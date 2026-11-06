module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.SetTheory.Cardinal.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatUniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindexSnd
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.SmoothNeighborhood
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStackIsFppfStack

/-!
# Artin's criterion: the size bound and the coproduct of charts

This file holds the size bound of Artin's criterion (Stacks 07Y4), the half of axiom [-1] its
proof uses, and the first steps of its assembly: the bound, from axiom [-1], on the finite type
fields over `S` that indexes the coproduct `U = ⨿ U_{k, x₀}` by a set, the coproduct of finite
type schemes as an object of the chosen big site, and the gluing of objects of a stack over a
disjoint étale cover.

## Main definitions

* `AlgebraicGeometry.Stack.IsSizeBounded`: the half of **axiom [-1]** of Artin's axioms that the
  proof uses, the set-theoretic condition of Stacks 07Y3 — the isomorphism classes of the fibres
  of `𝒳` over the finite type fields of `S` are bounded by the size of a single object of the
  chosen big site.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07Y3](https://stacks.math.columbia.edu/tag/07Y3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v v' v'' w z vX vI wI uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Axiom [-1], in the half the proof uses.** The supremum of the cardinalities of the sets of
isomorphism classes of objects of the fibres of `𝒳` over the finite type fields of `S` is at most
the size of one object of the chosen big fppf site.

The source's footnote to axiom [-1] also bounds the *arrows* of those fibres. That half is not
asked for: the proof of Stacks 07Y4 uses the bound only to index the coproduct
`U = ⨿ U_{k, x₀}` by a set, and indexing it by representatives of the isomorphism classes is
enough, so omitting it gives the stronger criterion. It is also the half a moduli stack can
satisfy here: an object of the stack of curves carries an algebraic space, a presheaf on the
site, and the presheaves isomorphic to a given one are not bounded by any object of the site. -/
public abbrev IsSizeBounded
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS)) : Prop :=
  ∃ T : AlgebraicGeometry.BigFppfOver B S hS,
    ∀ (U : AlgebraicGeometry.BigFppfOver B S hS) (k : Type u) [Field k],
      U.left.1 = Spec (.of k) →
      Deformation.Artin.IsFiniteTypeOver B S hS U →
      Cardinal.lift.{u, uX}
          (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
        Cardinal.lift.{uX, u} T.left.1.size

section BoundedFields

open Cardinal

private theorem exists_quotient_freeCommRing_equiv (κ : Cardinal.{u})
    (k : Type u) [Field k] (hk : #k ≤ κ) :
    ∃ I : Ideal (FreeCommRing κ.out), I.IsMaximal ∧
      Nonempty ((FreeCommRing κ.out ⧸ I) ≃+* k) := by
  obtain ⟨f⟩ : Nonempty (k ↪ κ.out) := (Cardinal.le_def _ _).mp (by simpa using hk)
  let g : κ.out → k := Function.invFun f
  have hg : Function.Surjective g := (Function.leftInverse_invFun f.injective).surjective
  let q : FreeCommRing κ.out →+* k := FreeCommRing.lift g
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := hg a
    exact ⟨FreeCommRing.of x, (FreeCommRing.lift_of g x).trans hx⟩
  exact ⟨RingHom.ker q, RingHom.ker_isMaximal_of_surjective q hq,
    ⟨RingHom.quotientKerEquivOfSurjective hq⟩⟩

private theorem maximalIdeals_freeCommRing_cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    #{I : Ideal (FreeCommRing κ.out) // I.IsMaximal} ≤ 2 ^ κ := by
  calc
    #{I : Ideal (FreeCommRing κ.out) // I.IsMaximal} ≤ #(Ideal (FreeCommRing κ.out)) :=
      Cardinal.mk_subtype_le _
    _ ≤ #(Set (FreeCommRing κ.out)) := Cardinal.mk_le_of_injective SetLike.coe_injective
    _ = 2 ^ κ := by rw [Cardinal.mk_set, Cardinal.mk_freeCommRing, Cardinal.mk_out,
      max_eq_left hκ]

private theorem quotient_freeCommRing_cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (I : Ideal (FreeCommRing κ.out)) : #(FreeCommRing κ.out ⧸ I) ≤ κ := by
  calc
    #(FreeCommRing κ.out ⧸ I) ≤ #(FreeCommRing κ.out) :=
      Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective
    _ = κ := by rw [Cardinal.mk_freeCommRing, Cardinal.mk_out, max_eq_left hκ]

private theorem ringHom_cardinal_le_two_power
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (A K : Type u) [NonAssocSemiring A] [NonAssocSemiring K]
    (hA : #A ≤ κ) (hK : #K ≤ κ) : #(A →+* K) ≤ 2 ^ κ := by
  calc
    #(A →+* K) ≤ #(A → K) := Cardinal.mk_le_of_injective DFunLike.coe_injective
    _ = #K ^ #A := by simp only [Cardinal.mk_arrow, Cardinal.lift_id]
    _ ≤ κ ^ κ := (Cardinal.power_le_power_right hK).trans
      (Cardinal.power_le_power_left (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ)) hA)
    _ = 2 ^ κ := Cardinal.power_self_eq hκ

private theorem sigma_cardinal_le {I : Type u} (F : I → Type u)
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ)
    (hF : ∀ i, #(F i) ≤ κ) : #(Σ i, F i) ≤ κ := by
  calc
    #(Σ i, F i) = Cardinal.sum (fun i => #(F i)) := Cardinal.mk_sigma F
    _ ≤ Cardinal.sum (fun _ : I => κ) := Cardinal.sum_le_sum _ _ hF
    _ = #I * κ := Cardinal.sum_const' I κ
    _ ≤ κ := Cardinal.mul_le_of_le hκ hI le_rfl

open AlgebraicGeometry CategoryTheory

private abbrev fieldBaseData (S : Scheme.{u}) :=
  Σ U : S.affineOpens,
    Σ I : {I : Ideal (FreeCommRing S.size.out) // I.IsMaximal},
      Γ(S, U.1) →+* (FreeCommRing S.size.out ⧸ I.1)

private theorem fieldBaseData_cardinal_le (S : Scheme.{u}) :
    #(fieldBaseData S) ≤ 2 ^ S.size := by
  have hκ : ℵ₀ ≤ 2 ^ S.size := S.aleph0_le_size.trans (Cardinal.cantor S.size).le
  exact sigma_cardinal_le _ hκ (S.mk_affineOpens_le_size.trans (Cardinal.cantor S.size).le)
    fun U => sigma_cardinal_le _ hκ
      (maximalIdeals_freeCommRing_cardinal_le S.size S.aleph0_le_size) fun I =>
        ringHom_cardinal_le_two_power S.size S.aleph0_le_size _ _ (S.mk_sections_le_size U)
          (quotient_freeCommRing_cardinal_le S.size S.aleph0_le_size I.1)

private def fieldBaseMap (S : Scheme.{u}) (d : fieldBaseData S) :
    Spec (.of (FreeCommRing S.size.out ⧸ d.2.1.1)) ⟶ S :=
  Spec.map (CommRingCat.ofHom d.2.2) ≫ d.1.2.fromSpec

private theorem exists_fieldBaseMap
    (S : Scheme.{u}) (k : Type u) [Field k] (f : Spec (.of k) ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (d : fieldBaseData S) (e : (FreeCommRing S.size.out ⧸ d.2.1.1) ≃+* k),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fieldBaseMap S d = f := by
  have hk : #k ≤ S.size := by
    have h := Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact f
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans h
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_quotient_freeCommRing_equiv S.size k hk
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f (IsLocalRing.closedPoint k) ∈ (⊤ : S.Opens) from trivial)
  have hrange : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    show f x ∈ U
    rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
    exact hx
  let g : Spec (.of k) ⟶ Spec Γ(S, U) := IsOpenImmersion.lift hU.fromSpec f hrange
  let ψ : Γ(S, U) →+* k := (Scheme.Spec.preimage g).unop.hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = g := Scheme.Spec.map_preimage g
  let φ := e.symm.toRingHom.comp ψ
  let d : fieldBaseData S := ⟨⟨U, hU⟩, ⟨I, hI⟩, φ⟩
  refine ⟨d, e, ?_⟩
  show Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) = f
  rw [← Category.assoc, ← Spec.map_comp]
  have hφ : CommRingCat.ofHom φ ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom ψ := by
    ext x
    exact e.apply_symm_apply (ψ x)
  rw [hφ, hψ]
  exact IsOpenImmersion.lift_fac hU.fromSpec f hrange

private abbrev finiteTypeFieldBaseData (S : Scheme.{u}) :=
  {d : fieldBaseData S // LocallyOfFiniteType (fieldBaseMap S d) ∧
    QuasiCompact (fieldBaseMap S d)}

@[instance_reducible] private def fieldBaseField (S : Scheme.{u}) (d : fieldBaseData S) :
    Field (FreeCommRing S.size.out ⧸ d.2.1.1) := by
  haveI : d.2.1.1.IsMaximal := d.2.1.2
  exact Ideal.Quotient.field d.2.1.1

private theorem fieldBase_spec_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (d : fieldBaseData S) :
    B.Contains (Spec (.of (FreeCommRing S.size.out ⧸ d.2.1.1))) := by
  show (Spec (.of (FreeCommRing S.size.out ⧸ d.2.1.1))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact (max_le S.aleph0_le_size
    (quotient_freeCommRing_cardinal_le S.size S.aleph0_le_size d.2.1.1)).trans_lt hS

private def fieldBaseOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (d : fieldBaseData S) : AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (fieldBaseMap S d) :
    B.obj (fieldBase_spec_mem B S hS d) ⟶ B.obj hS)

private theorem exists_finiteTypeFieldBaseMap
    (S : Scheme.{u}) (k : Type u) [Field k] (f : Spec (.of k) ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (d : finiteTypeFieldBaseData S)
      (e : (FreeCommRing S.size.out ⧸ d.1.2.1.1) ≃+* k),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fieldBaseMap S d.1 = f := by
  obtain ⟨d, e, he⟩ := exists_fieldBaseMap S k f
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    show IsIso (Scheme.Spec.map e.toCommRingCatIso.hom.op)
    infer_instance
  have hbase : fieldBaseMap S d = inv (Spec.map (CommRingCat.ofHom e.toRingHom)) ≫ f := by
    rw [← he, IsIso.inv_hom_id_assoc]
  refine ⟨⟨d, ?_, ?_⟩, e, he⟩ <;> rw [hbase] <;> infer_instance

private theorem small_cardinal_of_lift_le (C : Type w) (κ : Cardinal.{u})
    (h : Cardinal.lift.{u, w} #C ≤ Cardinal.lift.{w, u} κ) :
    ∃ hC : Small.{u} C, haveI := hC; #(Shrink.{u} C) ≤ κ := by
  have h' : Cardinal.lift.{u, w} #C ≤ Cardinal.lift.{w, u} #κ.out := by simpa using h
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp h'
  let hC : Small.{u} C := small_of_injective f.injective
  let := hC
  refine ⟨hC, ?_⟩
  have he : Function.Injective (fun x : Shrink.{u} C => f ((equivShrink C).symm x)) :=
    f.injective.comp (equivShrink C).symm.injective
  simpa using Cardinal.mk_le_of_injective he

end BoundedFields

private theorem exists_bounded_fieldFiber_index
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hsize : IsSizeBounded B S hS 𝒳) :
    ∃ I : Type u, Cardinal.mk I < B.cutoff ∧
      Nonempty (I ≃ (Σ d : finiteTypeFieldBaseData S,
        Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1))))) := by
  classical
  obtain ⟨T, hT⟩ := hsize
  have hbound (d : finiteTypeFieldBaseData S) :
      ∃ h : Small.{u}
          (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))),
        have := h
        Cardinal.mk (Shrink.{u}
          (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1))))) ≤
          T.left.1.size := by
    let : Field (FreeCommRing S.size.out ⧸ d.1.2.1.1) := fieldBaseField S d.1
    apply small_cardinal_of_lift_le _ T.left.1.size
    exact hT (fieldBaseOver B S hS d.1) (FreeCommRing S.size.out ⧸ d.1.2.1.1)
      rfl ⟨d.2.1, d.2.2⟩
  let hsmall (d : finiteTypeFieldBaseData S) := (hbound d).choose
  have hcard (d : finiteTypeFieldBaseData S) := (hbound d).choose_spec
  let (d : finiteTypeFieldBaseData S) :
      Small.{u} (Quotient (isIsomorphicSetoid
        (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))) := hsmall d
  let I := Σ d : finiteTypeFieldBaseData S,
    Shrink.{u} (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1))))
  let e : I ≃ (Σ d : finiteTypeFieldBaseData S,
      Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))) :=
    { toFun := fun i => ⟨i.1, (equivShrink
        (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS i.1.1))))).symm i.2⟩
      invFun := fun i => ⟨i.1, equivShrink
        (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS i.1.1)))) i.2⟩
      left_inv := by
        rintro ⟨d, x⟩
        exact congrArg (Sigma.mk d) ((equivShrink _).apply_symm_apply x)
      right_inv := by
        rintro ⟨d, x⟩
        exact congrArg (Sigma.mk d) ((equivShrink _).symm_apply_apply x) }
  refine ⟨I, ?_, ⟨e⟩⟩
  let κ := max (2 ^ S.size) T.left.1.size
  have hκ : Cardinal.aleph0 ≤ κ := T.left.1.aleph0_le_size.trans (le_max_right _ _)
  have hI : Cardinal.mk I ≤ κ := sigma_cardinal_le _ hκ
    (((Cardinal.mk_subtype_le _).trans (fieldBaseData_cardinal_le S)).trans (le_max_left _ _))
    fun d => (hcard d).trans (le_max_right _ _)
  exact hI.trans_lt (max_lt (B.cutoff_isStrongPrelimit hS) T.left.2)

private theorem eq_univ_of_isOpen_of_finiteTypePoints_subset
    {X : Scheme.{u}} {U : Set X} (hU : IsOpen U)
    (hpoints : ∀ x : X, AlgebraicGeometry.IsFiniteTypePoint x → x ∈ U) :
    U = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_contra hx
  obtain ⟨y, hy, hfinite⟩ := AlgebraicGeometry.inter_finiteTypePoints_nonempty
    hU.isClosed_compl.isLocallyClosed ⟨x, hx⟩
  exact hy (hpoints y hfinite)

private theorem isFiniteTypePoint_image_of_specField
    {k : Type u} [Field k] (f : Spec (.of k) ⟶ S)
    (hf : LocallyOfFiniteType f) :
    AlgebraicGeometry.IsFiniteTypePoint
      (f (IsLocalRing.closedPoint k)) := by
  obtain ⟨U, hU, x, hx, hclosed, _⟩ :=
    ((AlgebraicGeometry.finiteType_specField_tfae f).out 2 4).mp hf
  let s := f (IsLocalRing.closedPoint k)
  let g := S.fromSpecResidueField s
  have hspec : Scheme.SpecToEquivOfField (S.residueField s) S g =
      ⟨s, CommRingCat.ofHom (RingHom.id (S.residueField s))⟩ := by
    apply (Scheme.SpecToEquivOfField (S.residueField s) S).symm.injective
    rw [(Scheme.SpecToEquivOfField (S.residueField s) S).symm_apply_apply]
    show g = Spec.map (𝟙 (.of (S.residueField s))) ≫ S.fromSpecResidueField s
    rw [Spec.map_id, Category.id_comp]
  apply ((AlgebraicGeometry.finiteType_specField_tfae (k := S.residueField s) g).out 4 1).mp
  have hxs : (x : S) = s := hx
  have hmem : g (IsLocalRing.closedPoint (S.residueField s)) ∈ U.1 := by
    show ((Scheme.SpecToEquivOfField (S.residueField s) S) g).1 ∈ U.1
    rw [hspec, ← hxs]
    exact x.property
  refine ⟨U, (Scheme.preimage_eq_top_of_closedPoint_mem g hmem).ge, x, ?_,
    hclosed, ?_⟩
  · rw [hspec]
    exact hxs
  · rw [hspec]
    show Module.Finite (S.residueField s) (S.residueField s)
    infer_instance

open CategoryTheory.Limits

private theorem contains_coproduct_of_finiteType {ι : Type u}
    (U : ι → AlgebraicGeometry.BigFppfOver B S hS)
    (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i)) :
    B.Contains (∐ fun i => (U i).left.1) := by
  let κ := max (Cardinal.mk ι) S.size
  have hκ : κ < B.cutoff := max_lt hι hS
  apply lt_of_le_of_lt (schemeSize_coproduct_le _ κ
    (S.aleph0_le_size.trans (le_max_right _ _)) (le_max_left _ _) ?_) hκ
  intro i
  have : LocallyOfFiniteType (B.inclusion.map (U i).hom) := (hU i).1
  have : QuasiCompact (B.inclusion.map (U i).hom) := (hU i).2
  exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    (B.inclusion.map (U i).hom)).trans (le_max_right _ _)

private def finiteTypeCoproduct {ι : Type u}
    (U : ι → AlgebraicGeometry.BigFppfOver B S hS)
    (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i)) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (Sigma.desc (fun i => B.inclusion.map (U i).hom)) :
    B.obj (contains_coproduct_of_finiteType B S hS U hι hU) ⟶ B.obj hS)

private def finiteTypeCoproductι {ι : Type u}
    (U : ι → AlgebraicGeometry.BigFppfOver B S hS)
    (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i)) (i : ι) :
    U i ⟶ finiteTypeCoproduct B S hS U hι hU :=
  Over.homMk (ObjectProperty.homMk (Sigma.ι (fun j => (U j).left.1) i)) (by
    apply ObjectProperty.hom_ext
    exact Sigma.ι_desc _ _)

private theorem finiteTypeCoproductι_isOpenImmersion {ι : Type u}
    (U : ι → AlgebraicGeometry.BigFppfOver B S hS)
    (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i)) (i : ι) :
    AlgebraicGeometry.IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (finiteTypeCoproductι B S hS U hι hU i)) := by
  show AlgebraicGeometry.IsOpenImmersion (Sigma.ι (fun j => (U j).left.1) i)
  infer_instance

private theorem finiteTypeCoproductι_jointly_surjective {ι : Type u}
    (U : ι → AlgebraicGeometry.BigFppfOver B S hS)
    (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i))
    (x : (finiteTypeCoproduct B S hS U hι hU).left.1) :
    ∃ (i : ι) (y : (U i).left.1),
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (finiteTypeCoproductι B S hS U hι hU i)) y = x := by
  obtain ⟨⟨i, y⟩, h⟩ := (sigmaMk (fun i => (U i).left.1)).surjective x
  refine ⟨i, y, ?_⟩
  show Sigma.ι (fun j => (U j).left.1) i y = x
  exact (sigmaMk_mk (fun j => (U j).left.1) i y).symm.trans h

section DisjointCover
universe t

open CategoryTheory.Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion Fiber.mk
private theorem fiber_homs_of_empty_cover
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} {J : GrothendieckTopology C}
    (hp : p.IsStackInGroupoids.{t} J) {U : C} (hU : ⊥ ∈ J U)
    (x y : p.Fiber U) : Nonempty (x ≅ y) ∧ Subsingleton (x ⟶ y) := by
  have hg := hp.isFiberedInGroupoids.fiber_isGroupoid U
  have h := hp.isom_isSheaf x.1 y.1 x.2 y.2
    (fun e : PEmpty.{t + 1} => e.elim) (fun e => e.elim)
    (by simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using hU)
    (fun e _ => e.elim) (fun e _ => e.elim) (fun e _ => e.elim)
    (fun e _ => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e _ => e.elim) (fun e _ => e.elim)
  obtain ⟨f, hf, huniq⟩ := h (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e _ => e.elim)
  refine ⟨⟨fibreIsoMk hf.1 hf.2.1⟩, ⟨?_⟩⟩
  intro a b
  apply Fiber.hom_ext
  have ha := huniq a.1 ⟨fibreHom_of_fiberHom a,
    inferInstanceAs (IsIso (Fiber.fiberInclusion.map a)), fun e => e.elim⟩
  have hb := huniq b.1 ⟨fibreHom_of_fiberHom b,
    inferInstanceAs (IsIso (Fiber.fiberInclusion.map b)), fun e => e.elim⟩
  exact ha.trans hb.symm

private def disjointRestrictionIso
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} [p.IsFibered] {J : GrothendieckTopology C}
    (hp : p.IsStackInGroupoids.{t} J)
    {I : Type*} (V : I → C) (U : C) (f : ∀ i, V i ⟶ U)
    (hm : ∀ i, Mono (f i))
    (hd : ∀ {i j}, i ≠ j → ∀ {W : C} (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W)
    (xs : ∀ i, p.Fiber (V i))
    {W : C} (i j : I) (a : W ⟶ V i) (b : W ⟶ V j)
    (hab : a ≫ f i = b ≫ f j)
    (xr : Restriction p a (xs i).1 (xs i).2)
    (yr : Restriction p b (xs j).1 (xs j).2) :
    (Fiber.mk xr.hpt : p.Fiber W) ≅ (Fiber.mk yr.hpt : p.Fiber W) := by
  classical
  by_cases hij : i = j
  · subst j
    have : Mono (f i) := hm i
    have hab' : a = b := (cancel_mono (f i)).mp hab
    subst b
    exact xr.fiberIso.symm ≪≫ yr.fiberIso
  · exact (fiber_homs_of_empty_cover hp (hd hij a b hab) _ _).1.some

private theorem disjointRestrictionIso_self_fac
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} [p.IsFibered] {J : GrothendieckTopology C}
    (hp : p.IsStackInGroupoids.{t} J)
    {I : Type*} (V : I → C) (U : C) (f : ∀ i, V i ⟶ U)
    (hm : ∀ i, Mono (f i))
    (hd : ∀ {i j}, i ≠ j → ∀ {W : C} (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W)
    (xs : ∀ i, p.Fiber (V i))
    {W : C} (i : I) (a b : W ⟶ V i) (hab : a ≫ f i = b ≫ f i)
    (xr : Restriction p a (xs i).1 (xs i).2)
    (yr : Restriction p b (xs i).1 (xs i).2) :
    (disjointRestrictionIso hp V U f hm hd xs i i a b hab xr yr).hom.1 ≫ yr.hom =
      xr.hom := by
  have : Mono (f i) := hm i
  have hab' : a = b := (cancel_mono (f i)).mp hab
  subst b
  simp only [disjointRestrictionIso, dite_eq_left, Iso.trans_hom, Iso.symm_hom]
  show (Fiber.fiberInclusion.map xr.fiberIso.inv ≫
    Fiber.fiberInclusion.map yr.fiberIso.hom) ≫ yr.hom = _
  rw [Category.assoc]
  rw [Restriction.fiberIso_hom_fac, Restriction.fiberIso_inv_fac]

private theorem disjointRestrictionIso_restrict
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} [p.IsFibered] {J : GrothendieckTopology C}
    (hp : p.IsStackInGroupoids.{t} J)
    {I : Type*} (V : I → C) (U : C) (f : ∀ i, V i ⟶ U)
    (hm : ∀ i, Mono (f i))
    (hd : ∀ {i j}, i ≠ j → ∀ {W : C} (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W)
    (xs : ∀ i, p.Fiber (V i))
    {W Z : C} (i j : I) (a : W ⟶ V i) (b : W ⟶ V j)
    (hab : a ≫ f i = b ≫ f j)
    (g : Z ⟶ W) (c : Z ⟶ V i) (d : Z ⟶ V j)
    (hc : c = g ≫ a) (hd' : d = g ≫ b) (hcd : c ≫ f i = d ≫ f j)
    (xr : Restriction p a (xs i).1 (xs i).2)
    (yr : Restriction p b (xs j).1 (xs j).2)
    (xz : Restriction p c (xs i).1 (xs i).2)
    (yz : Restriction p d (xs j).1 (xs j).2) :
    IsRestrictionOf p g hc hd' xr yr xz yz
      (disjointRestrictionIso hp V U f hm hd xs i j a b hab xr yr).hom.1
      (disjointRestrictionIso hp V U f hm hd xs i j c d hcd xz yz).hom.1 := by
  let e := disjointRestrictionIso hp V U f hm hd xs i j a b hab xr yr
  let e' := disjointRestrictionIso hp V U f hm hd xs i j c d hcd xz yz
  have he : p.IsHomLift (𝟙 W) e.hom.1 := e.hom.2
  have he' : p.IsHomLift (𝟙 Z) e'.hom.1 := e'.hom.2
  have hcx := Restriction.isHomLift_compTo g a hc xr xz
  have hcy := Restriction.isHomLift_compTo g b hd' yr yz
  have hleft : p.IsHomLift g (e'.hom.1 ≫ Restriction.compTo p g b hd' yr yz) :=
    isHomLift_of_eq (n := 𝟙 Z ≫ g) inferInstance (Category.id_comp _)
  have hright : p.IsHomLift g (Restriction.compTo p g a hc xr xz ≫ e.hom.1) :=
    isHomLift_of_eq (n := g ≫ 𝟙 W) inferInstance (Category.comp_id _)
  show e'.hom.1 ≫ Restriction.compTo p g b hd' yr yz =
    Restriction.compTo p g a hc xr xz ≫ e.hom.1
  by_cases hij : i = j
  · subst j
    have hcart := yr.isStronglyCartesian_hom
    apply IsStronglyCartesian.ext p b yr.hom g
    rw [Category.assoc, Restriction.compTo_hom, disjointRestrictionIso_self_fac, Category.assoc,
      disjointRestrictionIso_self_fac, Restriction.compTo_hom]
  · exact hom_unique_of_fiber_isThin p g
      (fun x y => (fiber_homs_of_empty_cover hp (hd hij c d hcd) x y).2)
      _ _ hleft hright

private theorem disjointRestrictionIso_cocycle
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} [p.IsFibered] {J : GrothendieckTopology C}
    (hp : p.IsStackInGroupoids.{t} J)
    {I : Type*} (V : I → C) (U : C) (f : ∀ i, V i ⟶ U)
    (hm : ∀ i, Mono (f i))
    (hd : ∀ {i j}, i ≠ j → ∀ {W : C} (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W)
    (xs : ∀ i, p.Fiber (V i))
    {W : C} (i j k : I) (a : W ⟶ V i) (b : W ⟶ V j) (c : W ⟶ V k)
    (hab : a ≫ f i = b ≫ f j) (hbc : b ≫ f j = c ≫ f k)
    (xr : Restriction p a (xs i).1 (xs i).2)
    (yr : Restriction p b (xs j).1 (xs j).2)
    (zr : Restriction p c (xs k).1 (xs k).2) :
    (disjointRestrictionIso hp V U f hm hd xs i k a c (hab.trans hbc) xr zr).hom.1 =
      (disjointRestrictionIso hp V U f hm hd xs i j a b hab xr yr).hom.1 ≫
        (disjointRestrictionIso hp V U f hm hd xs j k b c hbc yr zr).hom.1 := by
  let e := disjointRestrictionIso hp V U f hm hd xs i k a c (hab.trans hbc) xr zr
  let e₁ := disjointRestrictionIso hp V U f hm hd xs i j a b hab xr yr
  let e₂ := disjointRestrictionIso hp V U f hm hd xs j k b c hbc yr zr
  have he : p.IsHomLift (𝟙 W) e.hom.1 := e.hom.2
  have he₁ : p.IsHomLift (𝟙 W) e₁.hom.1 := e₁.hom.2
  have he₂ : p.IsHomLift (𝟙 W) e₂.hom.1 := e₂.hom.2
  have hecomp : p.IsHomLift (𝟙 W) (e₁.hom.1 ≫ e₂.hom.1) :=
    isHomLift_of_eq (n := 𝟙 W ≫ 𝟙 W) inferInstance (Category.id_comp _)
  show e.hom.1 = e₁.hom.1 ≫ e₂.hom.1
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have hcart := zr.isStronglyCartesian_hom
      apply IsStronglyCartesian.ext p c zr.hom (𝟙 W)
      rw [disjointRestrictionIso_self_fac, Category.assoc,
        disjointRestrictionIso_self_fac, disjointRestrictionIso_self_fac]
    · exact hom_unique_of_fiber_isThin p (𝟙 W)
        (fun x y => (fiber_homs_of_empty_cover hp (hd hik a c (hab.trans hbc)) x y).2)
        _ _ he hecomp
  · exact hom_unique_of_fiber_isThin p (𝟙 W)
      (fun x y => (fiber_homs_of_empty_cover hp (hd hij a b hab) x y).2)
      _ _ he hecomp

private def chosenRestriction {C : Type u} [Category C]
    {D : Type w} [Category.{v} D] (p : D ⥤ C) [p.IsFibered]
    {U V : C} (x : p.Fiber U) (f : V ⟶ U) : Restriction p f x.1 x.2 :=
  Restriction.ofCartesian (pullbackFiber p x f).2 x.2
    (IsPreFibered.pullbackMap x.2 f) inferInstance

private theorem exists_fiber_of_disjoint_cover
    {C : Type u} [Category C] [HasPullbacks C] {D : Type w} [Category.{v} D]
    {p : D ⥤ C} {J : GrothendieckTopology C} (hp : p.IsStackInGroupoids.{t} J)
    {U : C} {I : Type t} (V : I → C) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    (hm : ∀ i, Mono (f i))
    (hd : ∀ {i j}, i ≠ j → ∀ {W : C} (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W)
    (xs : ∀ i, p.Fiber (V i)) :
    haveI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
    ∃ x : p.Fiber U, ∀ i, Nonempty (pullbackFiber p x (f i) ≅ xs i) := by
  classical
  let : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  let Vij i j := pullback (f i) (f j)
  let pr₁ i j : Vij i j ⟶ V i := pullback.fst _ _
  let pr₂ i j : Vij i j ⟶ V j := pullback.snd _ _
  have hij i j : IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j) :=
    IsPullback.of_hasPullback _ _
  let Vijk i j k := pullback (pr₂ i j) (pr₁ j k)
  let s₁₂ i j k : Vijk i j k ⟶ Vij i j := pullback.fst _ _
  let s₂₃ i j k : Vijk i j k ⟶ Vij j k := pullback.snd _ _
  have hijk i j k : IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k) :=
    IsPullback.of_hasPullback _ _
  let q₁ i j k := s₁₂ i j k ≫ pr₁ i j
  let q₂ i j k := s₁₂ i j k ≫ pr₂ i j
  let q₃ i j k := s₂₃ i j k ≫ pr₂ j k
  have hq12 i j k : q₁ i j k ≫ f i = q₂ i j k ≫ f j := by
    dsimp [q₁, q₂]
    rw [Category.assoc, Category.assoc, (hij i j).w]
  have hq23 i j k : q₂ i j k ≫ f j = q₃ i j k ≫ f k := by
    dsimp [q₂, q₃]
    rw [(hijk i j k).w, Category.assoc, Category.assoc, (hij j k).w]
  let xr i j := chosenRestriction p (xs i) (pr₁ i j)
  let yr i j := chosenRestriction p (xs j) (pr₂ i j)
  let wi i j k := chosenRestriction p (xs i) (q₁ i j k)
  let wj i j k := chosenRestriction p (xs j) (q₂ i j k)
  let wk i j k := chosenRestriction p (xs k) (q₃ i j k)
  let φ i j := disjointRestrictionIso hp V U f hm hd xs i j _ _ (hij i j).w (xr i j) (yr i j)
  let αij i j k := disjointRestrictionIso hp V U f hm hd xs i j _ _
    (hq12 i j k) (wi i j k) (wj i j k)
  let αjk i j k := disjointRestrictionIso hp V U f hm hd xs j k _ _
    (hq23 i j k) (wj i j k) (wk i j k)
  let αik i j k := disjointRestrictionIso hp V U f hm hd xs i k _ _
    ((hq12 i j k).trans (hq23 i j k)) (wi i j k) (wk i j k)
  let s₁₃ i j k : Vijk i j k ⟶ Vij i k :=
    pullback.lift (q₁ i j k) (q₃ i j k) ((hq12 i j k).trans (hq23 i j k))
  have hs₁ i j k : s₁₃ i j k ≫ pr₁ i k = q₁ i j k := pullback.lift_fst _ _ _
  have hs₃ i j k : s₁₃ i j k ≫ pr₂ i k = q₃ i j k := pullback.lift_snd _ _ _
  let dat : CategoryTheory.Functor.DescentDatum p V f Vij pr₁ pr₂ hij Vijk s₁₂ s₂₃ hijk q₁ q₂ q₃
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) :=
    { x := fun i => (xs i).1
      hx := fun i => (xs i).2
      xrij := xr
      xrji := yr
      φ := fun i j => (φ i j).hom.1
      φ_fibreHom := fun i j => fibreHom_of_fiberHom (φ i j).hom
      φ_iso := fun i j => inferInstanceAs (IsIso (Fiber.fiberInclusion.map (φ i j).hom))
      wi := wi
      wj := wj
      wk := wk
      αij := fun i j k => (αij i j k).hom.1
      αjk := fun i j k => (αjk i j k).hom.1
      αik := fun i j k => (αik i j k).hom.1
      αij_restr := fun i j k => disjointRestrictionIso_restrict hp V U f hm hd xs
        i j _ _ _ _ _ _ rfl rfl _ _ _ _ _
      αjk_restr := fun i j k => disjointRestrictionIso_restrict hp V U f hm hd xs
        j k _ _ _ _ _ _ (hijk i j k).w rfl _ _ _ _ _
      s₁₃ := s₁₃
      hs₁₃₁ := hs₁
      hs₁₃₂ := hs₃
      αik_restr := fun i j k => disjointRestrictionIso_restrict hp V U f hm hd xs
        i k _ _ _ _ _ _ (hs₁ i j k).symm (hs₃ i j k).symm _ _ _ _ _
      cocycle := fun i j k => disjointRestrictionIso_cocycle hp V U f hm hd xs
        i j k _ _ _ _ _ _ _ _ }
  obtain ⟨x, hx, r, ψ, hψ, hψiso, _⟩ := hp.effective_descent V f hf Vij pr₁ pr₂ hij
    Vijk s₁₂ s₂₃ hijk q₁ q₂ q₃ _ _ _ dat
  exact ⟨⟨x, hx⟩, fun i => ⟨(r i).fiberIso ≪≫ fibreIsoMk (hψ i) (hψiso i)⟩⟩

private lemma sieve_mem_of_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (E : PreZeroHypercover.{u + 1} V)
    (hE : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)) :
    E.sieve₀ ∈ ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) V := by
  let D := E.map (Over.forget (B.obj hS))
  have hD : AlgebraicGeometry.IsEtaleCovering ⟨V.left, D⟩ := hE
  obtain ⟨⟨T', D'⟩, hD', ht, heq⟩ :=
    AlgebraicGeometry.etaleCovering_has_representative B ⟨V.left, D⟩ hD
  cases ht
  obtain ⟨_, ⟨β, hX, hf⟩⟩ := heq
  have hle : D'.sieve₀ ≤ D.sieve₀ := by
    rw [Sieve.generate_le_iff]
    rintro Z f ⟨i⟩
    rw [hf i]
    exact D.sieve₀.downward_closed (D.sieve₀_f (β i)) (eqToHom (hX i))
  apply ((AlgebraicGeometry.etaleTopology B).mem_over_iff E.sieve₀).mpr
  show Sieve.overEquiv V (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact (AlgebraicGeometry.etaleTopology B).superset_covering hle
    (Precoverage.generate_mem_toGrothendieck ⟨D', rfl, hD'⟩)

private lemma etale_bot_mem_of_isEmpty
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)] :
    ⊥ ∈ ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) V := by
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := PEmpty, X := PEmpty.elim, f := fun i => i.elim }
  have he : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
      ⟨fun x => isEmptyElim x, fun i => PEmpty.elim i⟩
  simpa [E, PreZeroHypercover.sieve₀, Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using
    sieve_mem_of_etale B S hS E he

/-- Indexing a family of arrows by `ULift I` does not change the sieve it generates. -/
private lemma ofArrows_ulift_eq {C : Type*} [Category C] {I : Type u} {V : C}
    (X : I → C) (j : ∀ i, X i ⟶ V) :
    Sieve.ofArrows (fun i : ULift.{u + 1} I => X i.down) (fun i => j i.down) =
      Sieve.ofArrows X j := by
  apply le_antisymm <;> rw [Sieve.generate_le_iff]
  · rintro Z f ⟨i⟩
    exact Sieve.ofArrows_mk X j i.down
  · rintro Z f ⟨i⟩
    exact Sieve.ofArrows_mk (fun i : ULift.{u + 1} I => X i.down) (fun i => j i.down) (ULift.up i)

private lemma coproduct_etale_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (X : I → AlgebraicGeometry.BigFppfOver B S hS)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, X i ⟶ V)
    (e : (∐ (fun i => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (X i))) ≅
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)
    (he : ∀ i, Sigma.ι _ i ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)) :
    (∀ i, Mono (j i)) ∧
    Sieve.ofArrows X j ∈ ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) V ∧
    (∀ {i k}, i ≠ k → ∀ {Y : AlgebraicGeometry.BigFppfOver B S hS}
      (a : Y ⟶ X i) (b : Y ⟶ X k), a ≫ j i = b ≫ j k →
        ⊥ ∈ ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) Y) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let A := fun i => T.obj (X i)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have : Mono (T.map (j i)) := by rw [← he i]; infer_instance
    exact T.mono_of_mono_map inferInstance
  · let E : PreZeroHypercover.{u + 1} V :=
      { I₀ := ULift.{u + 1} I, X := fun i => X i.down, f := fun i => j i.down }
    have hE : (E.map T).presieve₀ ∈ Scheme.etalePrecoverage (T.obj V) := by
      refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨?_, ?_⟩
      · intro t
        obtain ⟨t, rfl⟩ := e.hom.homeomorph.surjective t
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk A).surjective t
        refine ⟨ULift.up i, x, ?_⟩
        show T.map (j i) x = _
        rw [← he i, Scheme.Hom.comp_apply, sigmaMk_mk]
        rfl
      · intro i
        show Etale (T.map (j i.down))
        rw [← he i.down]
        infer_instance
    have hh := sieve_mem_of_etale B S hS E hE
    rwa [show E.sieve₀ = Sieve.ofArrows X j from ofArrows_ulift_eq X j] at hh
  · intro i k hik Y a b hab
    have hh : T.map a ≫ Sigma.ι A i = T.map b ≫ Sigma.ι A k := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, he i, Category.assoc, he k, ← T.map_comp, ← T.map_comp, hab]
    have : IsEmpty (T.obj Y) := isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hik
    exact etale_bot_mem_of_isEmpty B S hS Y

private theorem schemeBelow_closed_under_isomorphisms (B : AlgebraicGeometry.BigFppfSite.{u}) :
    (AlgebraicGeometry.schemeSizeBelow B.cutoff).IsClosedUnderIsomorphisms :=
  ⟨by
    intro X Y e h
    show Y.size < B.cutoff
    rwa [← Scheme.size_congr e]⟩

private theorem schemeBelow_closed_under_pullbacks (B : AlgebraicGeometry.BigFppfSite.{u}) :
    (AlgebraicGeometry.schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape WalkingCospan := by
  have : (AlgebraicGeometry.schemeSizeBelow B.cutoff).IsClosedUnderIsomorphisms :=
    schemeBelow_closed_under_isomorphisms B
  exact .mk' (by
    rintro _ ⟨F, hF⟩
    show (limit F).size < B.cutoff
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

private theorem exists_fiber_of_coproduct
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {D : Type w} [Category.{v} D] (p : D ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsStackInGroupoids.{u + 1} ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    {I : Type u} (X : I → AlgebraicGeometry.BigFppfOver B S hS)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, X i ⟶ V)
    (e : (∐ (fun i => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (X i))) ≅
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)
    (he : ∀ i, Sigma.ι _ i ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i))
    (xs : ∀ i, p.Fiber (X i)) :
    haveI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
    ∃ x : p.Fiber V, ∀ i, Nonempty (pullbackFiber p x (j i) ≅ xs i) := by
  let : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  let : (AlgebraicGeometry.schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape WalkingCospan :=
    schemeBelow_closed_under_pullbacks B
  obtain ⟨hm, hj, hd⟩ := coproduct_etale_cover B S hS X V j e he
  let X' : ULift.{u + 1} I → AlgebraicGeometry.BigFppfOver B S hS := fun i => X i.down
  let j' : ∀ i, X' i ⟶ V := fun i => j i.down
  have hj' : Sieve.ofArrows X' j' ∈
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) V := by
    rwa [show Sieve.ofArrows X' j' = Sieve.ofArrows X j from ofArrows_ulift_eq X j]
  obtain ⟨x, hx⟩ := exists_fiber_of_disjoint_cover hp X' j' hj'
    (fun i => hm i.down) (fun {i k} hik {Y} a b hab =>
      hd (fun hh => hik (ULift.ext hh)) a b hab) (fun i => xs i.down)
  exact ⟨x, fun i => hx (ULift.up i)⟩

end DisjointCover

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeMulticrossBridge
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# Nodes and the fibre of the base change to the algebraic closure

A closed point `x` of a scheme `X` over a field `k` is a node when *some* point of
`X_{k̄}` above it is an ordinary double point, and the geometric form of the condition asks
that *every* such point be one.  Over an algebraically closed base field the base change is an
isomorphism, so the two agree and both agree with the condition that `𝒪_{X,x}` be a nodal
algebra.  Over a general field the gap between the two is a statement about the fibre, and this
file isolates it.

The engine is that over an algebraically closed field the ordinary-double-point condition is a
property of the local ring alone, at a closed point of a scheme locally of finite type.  That
is because the nodal-algebra condition of Tag 0C49 asks for a separable residue extension, for
reducedness and for a nondegenerate quadratic relation on the cotangent space, and over a
perfect base field the first of those is automatic while the other two do not mention the base
field at all.  Consequently the condition transports along a bare ring isomorphism of local
rings — in particular along an isomorphism of schemes which need not respect the structure
morphisms, and whose base fields need not even be the same field.

## Main results

* `Stacks.Curves.isNodalAlgebra_iff_isReduced_and_hasNodalQuadraticRelation` — over a perfect
  field the nodal-algebra condition is reducedness together with the quadratic relation.
* `Stacks.Curves.isNodalAlgebra_of_ringEquiv` — the nodal-algebra condition over perfect base
  fields transports along a ring isomorphism, with no compatibility of the algebra structures.
* `Stacks.Curves.isOrdinaryDoublePoint_of_ringEquiv_stalk` — being an ordinary double point
  depends only on the local ring.
* `Stacks.Curves.isOrdinaryDoublePoint_of_isIso` — its transport along an isomorphism of
  schemes over algebraically closed fields.
* `Stacks.Curves.isNode_iff_exists_isNodalAlgebra_stalk` and
  `Stacks.Curves.forall_isOrdinaryDoublePoint_iff` rewrite conditions (1) and (3) of Tag 0C4D as
  conditions on the local rings of the base change at the points above `x`.
* `Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive` — condition (1)
  implies condition (3) as soon as automorphisms of the base change act transitively on the
  points above `x`.
* `Stacks.Curves.isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed` — conditions (1) and (2) of Tag
  0C4D agree over an algebraically closed field.
* `Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode_of_isAlgClosed` — condition (1) implies
  condition (3) of Tag 0C4D over an algebraically closed field.

## Implementation notes

The `k`-algebra structure on a local ring of a scheme over `Spec k` is throughout the one
induced by the germ of the structure morphism, as in `Stacks.Curves.HasMulticrossCompletion`,
and the base change is the categorical pullback along `Spec k̄ ⟶ Spec k`, viewed over `Spec k̄`
through its second projection — the spellings used by `Stacks.Curves.IsNode`.

`Stacks.Curves.isOrdinaryDoublePoint_of_isIso` is strictly stronger than the transport
`Stacks.Curves.hasMulticrossCompletion_of_isIso`, which asks in addition for an isomorphism of
the two base fields, for a commuting square with it, and for a complete local model of the
source local ring: none of those are needed once the condition is known to be carried by the
local ring.

Instance search does not see through the `Scheme.Over` instance bound by a `let` in a
statement, so `LocallyOfFiniteType` for the base change viewed over `Spec k̄` is supplied by
`inferInstanceAs` against the second projection.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### The nodal-algebra condition over a perfect field -/

/-- **Over a perfect field the nodal-algebra condition of Tag 0C49 is reducedness together with
the nondegenerate quadratic relation.**  The separability clause is automatic, every extension
of a perfect field being separable in the sense of Tag 030O. -/
theorem isNodalAlgebra_iff_isReduced_and_hasNodalQuadraticRelation
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [IsLocalRing A]
    [Algebra k A] :
    IsNodalAlgebra k A ↔ IsReduced A ∧ HasNodalQuadraticRelation A :=
  ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨Algebra.isSeparableExtension_of_perfectField k (ResidueField A), h.1, h.2⟩⟩

/-- **Over perfect base fields, being a nodal algebra is a property of the ring alone.**  No
compatibility of the two algebra structures is required, and the two base fields need not be the
same field: the separability clause of Tag 0C49 is automatic over a perfect field, and the other
two clauses do not mention the base field. -/
theorem isNodalAlgebra_of_ringEquiv (k₁ : Type u) (k₂ : Type u) [Field k₁] [PerfectField k₁]
    [Field k₂] [PerfectField k₂] {A B : Type v} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra k₁ A] [Algebra k₂ B]
    (e : A ≃+* B) (h : IsNodalAlgebra k₁ A) : IsNodalAlgebra k₂ B := by
  rw [isNodalAlgebra_iff_isReduced_and_hasNodalQuadraticRelation] at h ⊢
  obtain ⟨_, hnod⟩ := h
  exact ⟨isReduced_of_injective e.symm.toRingHom e.symm.injective,
    hasNodalQuadraticRelation_of_ringEquiv e hnod⟩

/-! ### Ordinary double points depend only on the local ring -/

/-- **Over an algebraically closed field, being an ordinary double point is a property of the
local ring.**  Two closed points of schemes locally of finite type over algebraically closed
fields — not necessarily the same field — whose local rings are isomorphic as rings are ordinary
double points together. -/
theorem isOrdinaryDoublePoint_of_ringEquiv_stalk
    (K₁ : Type u) (K₂ : Type u) [Field K₁] [IsAlgClosed K₁] [Field K₂] [IsAlgClosed K₂]
    (X Y : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of K₁))]
    [Y.Over (AlgebraicGeometry.Spec (.of K₂))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of K₁))]
    [LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K₂))]
    (x : X) (y : Y) (hy : IsClosed ({y} : Set Y))
    (e : X.presheaf.stalk x ≃+* Y.presheaf.stalk y)
    (hx : IsOrdinaryDoublePoint K₁ X x) : IsOrdinaryDoublePoint K₂ Y y := by
  have hNX : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of K₁))
  have hNY : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ AlgebraicGeometry.Spec (.of K₂))
  let : Algebra K₁ (X.presheaf.stalk x) :=
    (((Scheme.ΓSpecIso (.of K₁)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of K₁)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom).toAlgebra
  let : Algebra K₂ (Y.presheaf.stalk y) :=
    (((Scheme.ΓSpecIso (.of K₂)).inv ≫ (Y ↘ AlgebraicGeometry.Spec (.of K₂)).appTop ≫
      Y.presheaf.germ ⊤ y trivial).hom).toAlgebra
  exact (isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K₂ Y y).mpr
    ⟨hy, isNodalAlgebra_of_ringEquiv K₁ K₂ e
      ((isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K₁ X x).mp hx).2⟩

/-- **Transport of the ordinary-double-point condition along an isomorphism of schemes over
algebraically closed fields.**  Neither a compatibility of the two structure morphisms nor an
isomorphism of the two base fields is required: the condition is carried by the local ring
alone, and closedness of the point is carried by the underlying homeomorphism. -/
theorem isOrdinaryDoublePoint_of_isIso
    (K₁ : Type u) (K₂ : Type u) [Field K₁] [IsAlgClosed K₁] [Field K₂] [IsAlgClosed K₂]
    (X Y : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of K₁))]
    [Y.Over (AlgebraicGeometry.Spec (.of K₂))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of K₁))]
    [LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K₂))]
    (h : Y ⟶ X) [IsIso h] (y : Y)
    (H : IsOrdinaryDoublePoint K₁ X (h.base y)) : IsOrdinaryDoublePoint K₂ Y y := by
  have hinj : Function.Injective h.base := (Scheme.homeoOfIso (asIso h)).injective
  have hy : IsClosed ({y} : Set Y) := by
    have hpre : h.base ⁻¹' {h.base y} = {y} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun z hz => hinj hz⟩
    rw [← hpre]
    exact H.1.preimage h.continuous
  exact isOrdinaryDoublePoint_of_ringEquiv_stalk K₁ K₂ X Y (h.base y) y hy
    (asIso (h.stalkMap y)).commRingCatIsoToRingEquiv H

/-! ### Conditions (1) and (3) of Tag 0C4D as conditions on the fibre -/

/-- Over `Spec k̄`, being an ordinary double point of the base change is the bridge condition of
`Stacks.Curves.isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk`. -/
private theorem isOrdinaryDoublePoint_pullback_iff
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (xbar : (pullback (X ↘ AlgebraicGeometry.Spec (.of k))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :
        Scheme.{u})) :
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
    let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
      pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
    letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
    IsOrdinaryDoublePoint K Y xbar ↔ IsClosed ({xbar} : Set Y) ∧
        (letI : Algebra K (Y.presheaf.stalk xbar) :=
           (((Scheme.ΓSpecIso (.of K)).inv ≫
               (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
                 Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
         IsNodalAlgebra K (Y.presheaf.stalk xbar)) := by
  intro K g Y q
  let instY : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have hlft : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g))
  exact isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K Y xbar

/-- **Condition (1) of Stacks 0C4D is the existence of a closed point of the base change above
`x` whose local ring is a nodal algebra.** -/
theorem isNode_iff_exists_isNodalAlgebra_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X) :
    IsNode k X x ↔
      let K := AlgebraicClosure k
      let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
      let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
      let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
        pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
      letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
      IsClosed ({x} : Set X) ∧ ∃ xbar : Y, p.base xbar = x ∧ IsClosed ({xbar} : Set Y) ∧
        (letI : Algebra K (Y.presheaf.stalk xbar) :=
           (((Scheme.ΓSpecIso (.of K)).inv ≫
               (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
                 Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
         IsNodalAlgebra K (Y.presheaf.stalk xbar)) := by
  show _ ↔ _
  exact and_congr_right fun _ => exists_congr fun xbar =>
    and_congr_right fun _ => isOrdinaryDoublePoint_pullback_iff k X xbar

/-- **Condition (3) of Stacks 0C4D is the statement that every point of the base change above
`x` is closed with nodal local ring.** -/
theorem forall_isOrdinaryDoublePoint_iff
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X) :
    (let K := AlgebraicClosure k
      let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
      let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
      let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
        pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
      letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
      ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar) ↔
      (let K := AlgebraicClosure k
      let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
      let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
      let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
        pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
      letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
      ∀ xbar : Y, p.base xbar = x → IsClosed ({xbar} : Set Y) ∧
        (letI : Algebra K (Y.presheaf.stalk xbar) :=
           (((Scheme.ΓSpecIso (.of K)).inv ≫
               (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
                 Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
         IsNodalAlgebra K (Y.presheaf.stalk xbar))) := by
  show _ ↔ _
  exact forall_congr' fun xbar => imp_congr_right fun _ =>
    isOrdinaryDoublePoint_pullback_iff k X xbar

/-- **Condition (1) of Stacks 0C4D implies condition (3) as soon as the automorphisms of the
base change act transitively on the points above `x`.**  An isomorphism of the base change with
itself carrying one point above `x` to another transports both closedness of the point and the
ordinary-double-point condition, by
`Stacks.Curves.isOrdinaryDoublePoint_of_isIso`; the isomorphism is not required to lie over
`X`. -/
theorem forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X)
    (htrans :
      let K := AlgebraicClosure k
      let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
      let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
      ∀ xbar xbar' : Y, p.base xbar = x → p.base xbar' = x →
        ∃ h : Y ⟶ Y, IsIso h ∧ h.base xbar = xbar')
    (hnode : IsNode k X x) :
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
    let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
      pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
    letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
    ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar := by
  intro K g Y p q xbar hxbar
  let instY : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  obtain ⟨-, xbar0, hxbar0, hodp0⟩ := hnode
  have hlft : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g))
  obtain ⟨h, _, hh⟩ := htrans xbar xbar0 hxbar hxbar0
  exact isOrdinaryDoublePoint_of_isIso K K Y Y h xbar (hh ▸ hodp0)

/-! ### The case of an algebraically closed base field -/

/-- Over an algebraically closed field the morphism to be based changed along is an
isomorphism. -/
theorem isIso_specMap_algebraMap_algebraicClosure (k : Type u) [Field k] [IsAlgClosed k] :
    IsIso (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) := by
  have hψ : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  infer_instance

/-- **Conditions (1) and (2) of Stacks 0C4D agree over an algebraically closed field:** a closed
point of a scheme locally of finite type over an algebraically closed field is a node exactly
when its local ring is a nodal algebra.

Over an algebraically closed field the base change to the algebraic closure is an isomorphism,
so the point above `x` is unique and its local ring is isomorphic to `𝒪_{X,x}`; the
ordinary-double-point condition then moves between the two by
`Stacks.Curves.isOrdinaryDoublePoint_of_isIso`, and the comparison with the nodal-algebra
condition is `Stacks.Curves.isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk`. -/
theorem isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    (IsNode k X x ↔ IsNodalAlgebra k (X.presheaf.stalk x)) := by
  intro kToStalk
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hgiso : IsIso g := isIso_specMap_algebraMap_algebraicClosure k
  let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
    pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
  let instY : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have hpiso : IsIso p := inferInstanceAs (IsIso (pullback.fst _ g))
  have hlft : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g))
  have hbridge := isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk k X x
  constructor
  · rintro ⟨-, xbar, hxbar, hodp⟩
    refine (hbridge.mp ?_).2
    have hx' : (inv p).base x = xbar := by
      have hc := Scheme.Hom.comp_apply p (inv p) xbar
      rw [IsIso.hom_inv_id] at hc
      rw [← hxbar, ← hc]
      rfl
    exact isOrdinaryDoublePoint_of_isIso K k Y X (inv p) x (hx' ▸ hodp)
  · intro hnodal
    have hodpX : IsOrdinaryDoublePoint k X x := hbridge.mpr ⟨hx, hnodal⟩
    have hc : x = p.base ((inv p).base x) := by
      have h0 := Scheme.Hom.comp_apply (inv p) p x
      rw [IsIso.inv_hom_id] at h0
      simpa using h0
    exact ⟨hx, (inv p).base x, hc.symm,
      isOrdinaryDoublePoint_of_isIso k K X Y p ((inv p).base x) (hc ▸ hodpX)⟩

/-- **Condition (1) of Stacks 0C4D implies condition (3) over an algebraically closed field.**
The base change is then an isomorphism, so there is only one point above `x` and the
existential of condition (1) is already universally quantified. -/
theorem forall_isOrdinaryDoublePoint_of_isNode_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X)
    (hnode : IsNode k X x) :
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
    let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
      pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
    letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
    ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar :=
  forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive k X x
    (by
      intro K g Y p xbar xbar' h1 h2
      have hgiso : IsIso g := isIso_specMap_algebraMap_algebraicClosure k
      have hpiso : IsIso p := inferInstanceAs (IsIso (pullback.fst _ g))
      exact ⟨𝟙 Y, inferInstance, by
        simpa using (Scheme.homeoOfIso (asIso p)).injective (h1.trans h2.symm)⟩)
    hnode

end Stacks.Curves

end

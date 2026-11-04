module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Module.End
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The completed group algebra of a topological group

Let `Λ` be a ring, not necessarily commutative, and `G` a topological group. The completed group
algebra `Λ[[G]]` is the limit of the group algebras `Λ[G/U]` over the open normal subgroups `U` of
`G`, the transition maps being induced by the quotient maps `G/U → G/V` for `U ≤ V`. For a
profinite group these are the group algebras of the finite quotients of `G`, and this is the ring
`Λ[[G]]` of [Stacks, Tag 03VI].

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `CompletedGroupAlgebra Λ G`: the ring `Λ[[G]]`, realised as the subring of compatible families in
  `∏_U Λ[G/U]`.
* `CompletedGroupAlgebra.eval`: the projection `Λ[[G]] → Λ[G/U]`.
* `CompletedGroupAlgebra.map`: the ring homomorphism `Λ[[G]] → Λ[[H]]` induced by a continuous
  homomorphism `G → H`, and `CompletedGroupAlgebra.mapRingEquiv` the ring isomorphism induced by an
  isomorphism of topological groups.
* `CompletedGroupAlgebra.augmentation`: the augmentation `Λ[[G]] → Λ`.
* `CompletedGroupAlgebra.const`: the inclusion of the constants `Λ → Λ[[G]]`.
* `CompletedGroupAlgebra.of`: the image of a group element.
* `CompletedGroupAlgebra.toAddMonoidEnd`: the action of `Λ[[G]]` on a `Λ`-module with an action of
  `G` that is trivial on an open normal subgroup.

## Main results

* `exists_openNormalSubgroup_smul_eq`: a finite module with a continuous action of a compact group
  is acted on trivially by some open normal subgroup.

## Implementation notes

The component of `map f x` at an open normal subgroup `V` of `H` is the image of the component of
`x` at the preimage of `V`, so no transport along equalities of open subgroups is needed.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.GroupHomology

open MonoidAlgebra

section Transition

variable (Λ : Type u) [Ring Λ] {G : Type v} [Group G] [TopologicalSpace G]

/-- The ring homomorphism `Λ[G/U] → Λ[G/V]` induced by an inclusion `U ≤ V` of open normal
subgroups. -/
public def quotientAlgebraMap {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) →+* MonoidAlgebra Λ (G ⧸ (V : Subgroup G)) :=
  mapDomainRingHom Λ (QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx => h hx)

/-- The transition map sends `δ_{gU} a` to `δ_{gV} a`. -/
@[simp]
public theorem quotientAlgebraMap_single {U V : OpenNormalSubgroup G} (h : U ≤ V) (g : G)
    (a : Λ) :
    quotientAlgebraMap Λ h (single (g : G ⧸ (U : Subgroup G)) a) =
      single (g : G ⧸ (V : Subgroup G)) a := by
  rw [quotientAlgebraMap, mapDomainRingHom_apply, mapDomain_single]
  rfl

/-- The transition map sends `δ_1 a` to `δ_1 a`. -/
@[simp]
public theorem quotientAlgebraMap_single_one {U V : OpenNormalSubgroup G} (h : U ≤ V) (a : Λ) :
    quotientAlgebraMap Λ h (single (1 : G ⧸ (U : Subgroup G)) a) =
      single (1 : G ⧸ (V : Subgroup G)) a := by
  simpa using quotientAlgebraMap_single Λ h 1 a

end Transition

variable (Λ : Type u) [Ring Λ] (G : Type v) [Group G] [TopologicalSpace G]

/-- The subring of compatible families in `∏_U Λ[G/U]`, the product over the open normal subgroups
`U` of `G`. -/
public def completedGroupAlgebraSubring :
    Subring (∀ U : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ (U : Subgroup G))) where
  carrier := {x | ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V), quotientAlgebraMap Λ h (x U) = x V}
  mul_mem' {a b} ha hb U V h := by
    simp only [Set.mem_ofPred_eq, Pi.mul_apply, map_mul] at *
    rw [ha h, hb h]
  one_mem' U V h := by simp
  add_mem' {a b} ha hb U V h := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [ha h, hb h]
  zero_mem' U V h := by simp
  neg_mem' {a} ha U V h := by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, map_neg] at *
    rw [ha h]

/-- **The completed group algebra** `Λ[[G]]`: the limit of the group algebras `Λ[G/U]` over the
open normal subgroups `U` of `G`. -/
public abbrev CompletedGroupAlgebra : Type (max u v) :=
  ↥(completedGroupAlgebraSubring Λ G)

namespace CompletedGroupAlgebra

variable {Λ G}

/-- The projection `Λ[[G]] → Λ[G/U]`. -/
public def eval (U : OpenNormalSubgroup G) :
    CompletedGroupAlgebra Λ G →+* MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) :=
  (Pi.evalRingHom _ U).comp (completedGroupAlgebraSubring Λ G).subtype

/-- The projection to `Λ[G/U]` is the component at `U` of the compatible family. -/
public theorem eval_apply (U : OpenNormalSubgroup G) (x : CompletedGroupAlgebra Λ G) :
    eval U x = (x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ (U : Subgroup G))) U :=
  rfl

/-- The components of an element of `Λ[[G]]` are compatible. -/
public theorem quotientAlgebraMap_eval {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (x : CompletedGroupAlgebra Λ G) : quotientAlgebraMap Λ h (eval U x) = eval V x :=
  x.2 h

/-- Two elements of `Λ[[G]]` with the same components are equal. -/
public theorem ext {x y : CompletedGroupAlgebra Λ G} (h : ∀ U, eval U x = eval U y) : x = y :=
  Subtype.ext (funext h)

/-- An element of `Λ[[G]]` built from a compatible family. -/
public def mk (x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ (U : Subgroup G)))
    (hx : ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V), quotientAlgebraMap Λ h (x U) = x V) :
    CompletedGroupAlgebra Λ G :=
  ⟨x, hx⟩

/-- The component at `U` of the element built from a compatible family is its member at `U`. -/
@[simp]
public theorem eval_mk (x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ (U : Subgroup G)))
    (hx) (U : OpenNormalSubgroup G) : eval U (mk x hx) = x U :=
  rfl

/-- The constants `Λ → Λ[[G]]`. -/
public def const : Λ →+* CompletedGroupAlgebra Λ G :=
  (RingHom.pi fun _ => singleOneRingHom).codRestrict _ fun a _U _V h =>
    quotientAlgebraMap_single_one Λ h a

/-- The component at `U` of the constant `a` is `δ_1 a`. -/
@[simp]
public theorem eval_const (U : OpenNormalSubgroup G) (a : Λ) :
    eval U (const a) = single (1 : G ⧸ (U : Subgroup G)) a :=
  rfl

/-- The image of a group element in `Λ[[G]]`. -/
public def of : G →* CompletedGroupAlgebra Λ G where
  toFun g := mk (fun U => single (g : G ⧸ (U : Subgroup G)) 1) fun U V h => by simp
  map_one' := ext fun U => by simp [MonoidAlgebra.one_def]
  map_mul' g h := ext fun U => by simp [QuotientGroup.mk_mul, MonoidAlgebra.single_mul_single]

/-- The component at `U` of a group element `g` is `δ_{gU}`. -/
@[simp]
public theorem eval_of (U : OpenNormalSubgroup G) (g : G) :
    eval U (of g : CompletedGroupAlgebra Λ G) = single (g : G ⧸ (U : Subgroup G)) 1 :=
  rfl

/-- The constants commute with the group elements. -/
public theorem const_mul_of (a : Λ) (g : G) :
    (const a : CompletedGroupAlgebra Λ G) * of g = of g * const a :=
  ext fun U => by simp [MonoidAlgebra.single_mul_single]

/-- The augmentation `Λ[H] → Λ` of a group algebra, sending every group element to `1`. -/
public def finiteAugmentation (H : Type*) [Group H] : MonoidAlgebra Λ H →+* Λ :=
  liftNCRingHom (RingHom.id Λ) (1 : H →* Λ) fun _ _ => Commute.one_right _

/-- The augmentation sends `δ_h a` to `a`. -/
@[simp]
public theorem finiteAugmentation_single {H : Type*} [Group H] (h : H) (a : Λ) :
    finiteAugmentation (Λ := Λ) H (single h a) = a := by
  simp [finiteAugmentation, liftNCRingHom, liftNC_single]

/-- Two ring homomorphisms out of `Λ[G/U]` agreeing on every `δ_{gU} a` are equal. -/
private theorem quotient_ringHom_ext {U : OpenNormalSubgroup G} {S : Type*} [Semiring S]
    {φ ψ : MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) →+* S}
    (h : ∀ (g : G) (a : Λ), φ (single (g : G ⧸ (U : Subgroup G)) a) =
      ψ (single (g : G ⧸ (U : Subgroup G)) a)) : φ = ψ := by
  refine MonoidAlgebra.ringHom_ext (fun a => ?_) (fun g => ?_)
  · simpa [← QuotientGroup.mk_one] using h 1 a
  · induction g using QuotientGroup.induction_on with
    | H g => exact h g 1

/-- The augmentations of `Λ[G/U]` and `Λ[G/V]` are compatible with the transition map. -/
public theorem finiteAugmentation_comp_quotientAlgebraMap {U V : OpenNormalSubgroup G}
    (h : U ≤ V) :
    (finiteAugmentation (G ⧸ (V : Subgroup G))).comp (quotientAlgebraMap Λ h) =
      finiteAugmentation (G ⧸ (U : Subgroup G)) :=
  quotient_ringHom_ext fun g a => by simp [quotientAlgebraMap]

variable [IsTopologicalGroup G]

/-- The open normal subgroup `G` itself. -/
public def topSubgroup : OpenNormalSubgroup G :=
  { toOpenSubgroup := ⊤, isNormal' := by simp }

/-- The augmentation `Λ[[G]] → Λ`, sending every group element to `1`. -/
public def augmentation : CompletedGroupAlgebra Λ G →+* Λ :=
  (finiteAugmentation (G ⧸ ((topSubgroup : OpenNormalSubgroup G) : Subgroup G))).comp
    (eval topSubgroup)

omit [IsTopologicalGroup G] in
/-- The augmentation is computed on any component. -/
public theorem augmentation_eq (U : OpenNormalSubgroup G) (x : CompletedGroupAlgebra Λ G) :
    augmentation x = finiteAugmentation _ (eval U x) := by
  have hU : U ≤ topSubgroup := fun _ _ => trivial
  rw [augmentation, RingHom.comp_apply, ← quotientAlgebraMap_eval hU, ← RingHom.comp_apply,
    finiteAugmentation_comp_quotientAlgebraMap]

omit [IsTopologicalGroup G] in
/-- The augmentation of the constant `a` is `a`. -/
@[simp]
public theorem augmentation_const (a : Λ) :
    augmentation (const a : CompletedGroupAlgebra Λ G) = a := by
  rw [augmentation, RingHom.comp_apply, eval_const, finiteAugmentation_single]

omit [IsTopologicalGroup G] in
/-- The augmentation of a group element is `1`. -/
@[simp]
public theorem augmentation_of (g : G) : augmentation (of g : CompletedGroupAlgebra Λ G) = 1 := by
  rw [augmentation, RingHom.comp_apply, eval_of, finiteAugmentation_single]

omit [IsTopologicalGroup G] in
/-- The augmentation restricts to the identity on the constants. -/
public theorem augmentation_comp_const :
    (augmentation : CompletedGroupAlgebra Λ G →+* Λ).comp const = RingHom.id Λ := by
  ext a; simp

end CompletedGroupAlgebra

/-! ### Functoriality -/

namespace CompletedGroupAlgebra

variable {Λ} {G} {H : Type w} [Group H] [TopologicalSpace H] {K : Type*} [Group K]
  [TopologicalSpace K]

/-- The preimage of an open normal subgroup under a continuous homomorphism. -/
public def comapSubgroup (f : G →* H) (hf : Continuous f) (V : OpenNormalSubgroup H) :
    OpenNormalSubgroup G :=
  { toOpenSubgroup := OpenSubgroup.comap f hf V.toOpenSubgroup
    isNormal' := (V.isNormal').comap f }

/-- `g` lies in the preimage of `V` if and only if `f g` lies in `V`. -/
@[simp]
public theorem mem_comapSubgroup {f : G →* H} {hf : Continuous f} {V : OpenNormalSubgroup H}
    {g : G} : g ∈ comapSubgroup f hf V ↔ f g ∈ V :=
  Iff.rfl

/-- `f` maps the preimage of `V` into `V`. -/
public theorem map_mem_of_mem_comapSubgroup (f : G →* H) (hf : Continuous f)
    (V : OpenNormalSubgroup H) : ∀ g ∈ comapSubgroup f hf V, f g ∈ V :=
  fun _ h => mem_comapSubgroup.1 h

/-- The ring homomorphism `Λ[G/f⁻¹V] → Λ[H/V]` induced by `f`. -/
public def quotientMapAlgebra (f : G →* H) {U : OpenNormalSubgroup G} {V : OpenNormalSubgroup H}
    (h : ∀ g ∈ U, f g ∈ V) :
    MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) →+* MonoidAlgebra Λ (H ⧸ (V : Subgroup H)) :=
  mapDomainRingHom Λ (QuotientGroup.map _ _ f h)

/-- The map induced by `f` sends `δ_{gU} a` to `δ_{f(g)V} a`. -/
@[simp]
public theorem quotientMapAlgebra_single (f : G →* H) {U : OpenNormalSubgroup G}
    {V : OpenNormalSubgroup H} (h : ∀ g ∈ U, f g ∈ V) (g : G) (a : Λ) :
    quotientMapAlgebra f h (single (g : G ⧸ (U : Subgroup G)) a) =
      single (f g : H ⧸ (V : Subgroup H)) a := by
  rw [quotientMapAlgebra, mapDomainRingHom_apply, mapDomain_single]
  rfl

/-- The map `Λ[G/U] → Λ[H/V]` induced by `f`, after the transition map `Λ[G/U'] → Λ[G/U]`, is the
map `Λ[G/U'] → Λ[H/V]` induced by `f`. -/
public theorem quotientMapAlgebra_comp_quotientAlgebraMap (f : G →* H)
    {U U' : OpenNormalSubgroup G} {V : OpenNormalSubgroup H} (hU : U' ≤ U)
    (h : ∀ g ∈ U, f g ∈ V) (h' : ∀ g ∈ U', f g ∈ V) :
    (quotientMapAlgebra (Λ := Λ) f h).comp (quotientAlgebraMap Λ hU) = quotientMapAlgebra f h' :=
  quotient_ringHom_ext fun g a => by simp

/-- The transition map `Λ[H/V] → Λ[H/V']`, after the map `Λ[G/U] → Λ[H/V]` induced by `f`, is the
map `Λ[G/U] → Λ[H/V']` induced by `f`. -/
public theorem quotientAlgebraMap_comp_quotientMapAlgebra (f : G →* H)
    {U : OpenNormalSubgroup G} {V V' : OpenNormalSubgroup H} (hV : V ≤ V')
    (h : ∀ g ∈ U, f g ∈ V) (h' : ∀ g ∈ U, f g ∈ V') :
    (quotientAlgebraMap Λ hV).comp (quotientMapAlgebra (Λ := Λ) f h) = quotientMapAlgebra f h' :=
  quotient_ringHom_ext fun g a => by simp

/-- Two ring homomorphisms out of `Λ[G/U]` and `Λ[G/U']` that agree on `Λ[G/(U ⊓ U')]` have the
same value on the components of any element of `Λ[[G]]`. -/
private theorem apply_eval_eq_of_comp_eq {U U' : OpenNormalSubgroup G} {S : Type*} [Semiring S]
    {φ : MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) →+* S}
    {φ' : MonoidAlgebra Λ (G ⧸ (U' : Subgroup G)) →+* S}
    (h : φ.comp (quotientAlgebraMap Λ (inf_le_left : U ⊓ U' ≤ U)) =
      φ'.comp (quotientAlgebraMap Λ (inf_le_right : U ⊓ U' ≤ U')))
    (x : CompletedGroupAlgebra Λ G) : φ (eval U x) = φ' (eval U' x) := by
  rw [← quotientAlgebraMap_eval (inf_le_left : U ⊓ U' ≤ U) x,
    ← quotientAlgebraMap_eval (inf_le_right : U ⊓ U' ≤ U') x]
  exact DFunLike.congr_fun h _

/-- The component at `V` of the image of `x` under `f` may be computed from the component of `x` at
any open normal subgroup mapped into `V`. -/
public theorem quotientMapAlgebra_eval (f : G →* H) {U U' : OpenNormalSubgroup G}
    {V : OpenNormalSubgroup H} (h : ∀ g ∈ U, f g ∈ V) (h' : ∀ g ∈ U', f g ∈ V)
    (x : CompletedGroupAlgebra Λ G) :
    quotientMapAlgebra f h (eval U x) = quotientMapAlgebra f h' (eval U' x) := by
  have hW : ∀ g ∈ U ⊓ U', f g ∈ V := fun g hg => h g hg.1
  exact apply_eval_eq_of_comp_eq
    ((quotientMapAlgebra_comp_quotientAlgebraMap f inf_le_left h hW).trans
      (quotientMapAlgebra_comp_quotientAlgebraMap f inf_le_right h' hW).symm) x

/-- The ring homomorphism `Λ[[G]] → Λ[[H]]` induced by a continuous homomorphism `G → H`. -/
public def map (f : G →* H) (hf : Continuous f) :
    CompletedGroupAlgebra Λ G →+* CompletedGroupAlgebra Λ H :=
  (RingHom.pi fun V => (quotientMapAlgebra (Λ := Λ) f
      (map_mem_of_mem_comapSubgroup f hf V)).comp
    (eval (comapSubgroup f hf V))).codRestrict _ fun x V V' hV => by
    change quotientAlgebraMap Λ hV (quotientMapAlgebra f (map_mem_of_mem_comapSubgroup f hf V)
        (eval (comapSubgroup f hf V) x)) =
      quotientMapAlgebra f (map_mem_of_mem_comapSubgroup f hf V') (eval (comapSubgroup f hf V') x)
    exact (DFunLike.congr_fun (quotientAlgebraMap_comp_quotientMapAlgebra (Λ := Λ) f hV
      (map_mem_of_mem_comapSubgroup f hf V) fun g hg =>
        hV (map_mem_of_mem_comapSubgroup f hf V g hg)) _).trans
      (quotientMapAlgebra_eval _ _ _ x)

/-- The component at `V` of `map f x` is computed from any component of `x` mapped into `V`. -/
public theorem eval_map (f : G →* H) (hf : Continuous f) {U : OpenNormalSubgroup G}
    {V : OpenNormalSubgroup H} (h : ∀ g ∈ U, f g ∈ V) (x : CompletedGroupAlgebra Λ G) :
    eval V (map f hf x) = quotientMapAlgebra f h (eval U x) :=
  quotientMapAlgebra_eval _ _ _ x

/-- The map induced by `f` sends the group element `g` to `f g`. -/
@[simp]
public theorem map_of (f : G →* H) (hf : Continuous f) (g : G) :
    map f hf (of g : CompletedGroupAlgebra Λ G) = of (f g) :=
  ext fun V => by
    rw [eval_map f hf (U := comapSubgroup f hf V) (map_mem_of_mem_comapSubgroup f hf V),
      eval_of, eval_of]
    exact quotientMapAlgebra_single (Λ := Λ) f _ g 1

/-- The map induced by `f` fixes the constants. -/
@[simp]
public theorem map_const (f : G →* H) (hf : Continuous f) (a : Λ) :
    map f hf (const a : CompletedGroupAlgebra Λ G) = const a :=
  ext fun V => by
    rw [eval_map f hf (U := comapSubgroup f hf V) (map_mem_of_mem_comapSubgroup f hf V),
      eval_const, eval_const]
    simpa using quotientMapAlgebra_single (Λ := Λ) f (U := comapSubgroup f hf V)
      (map_mem_of_mem_comapSubgroup f hf V) 1 a

/-- The map induced by the identity is the identity. -/
public theorem map_id (x : CompletedGroupAlgebra Λ G) :
    map (MonoidHom.id G) continuous_id x = x :=
  ext fun U => by
    have h : quotientMapAlgebra (Λ := Λ) (MonoidHom.id G) (U := U) (V := U)
        (fun g hg => by simpa using hg) =
        quotientAlgebraMap Λ le_rfl :=
      quotient_ringHom_ext fun g a => by simp
    rw [eval_map _ _ (U := U) (fun g hg => by simpa using hg), h]
    exact quotientAlgebraMap_eval _ x

/-- The map induced by `g ∘ f` is the composite of the maps induced by `f` and `g`. -/
public theorem map_map (f : G →* H) (hf : Continuous f) (g : H →* K) (hg : Continuous g)
    (x : CompletedGroupAlgebra Λ G) :
    map g hg (map f hf x) = map (g.comp f) (hg.comp hf) x :=
  ext fun W => by
    have h : (quotientMapAlgebra (Λ := Λ) g (map_mem_of_mem_comapSubgroup g hg W)).comp
        (quotientMapAlgebra f (map_mem_of_mem_comapSubgroup f hf (comapSubgroup g hg W))) =
        quotientMapAlgebra (g.comp f) (U := comapSubgroup f hf (comapSubgroup g hg W))
          fun x hx => map_mem_of_mem_comapSubgroup g hg W _
            (map_mem_of_mem_comapSubgroup f hf _ x hx) :=
      quotient_ringHom_ext fun g a => by
        rw [RingHom.comp_apply, quotientMapAlgebra_single, quotientMapAlgebra_single,
          quotientMapAlgebra_single]
        rfl
    rw [eval_map _ _ (map_mem_of_mem_comapSubgroup g hg W),
      eval_map _ _ (map_mem_of_mem_comapSubgroup f hf (comapSubgroup g hg W)),
      eval_map _ _ (U := comapSubgroup f hf (comapSubgroup g hg W)) fun x hx =>
        map_mem_of_mem_comapSubgroup g hg W _ (map_mem_of_mem_comapSubgroup f hf _ x hx)]
    exact DFunLike.congr_fun h _

/-- Equal continuous homomorphisms induce equal maps. -/
public theorem map_congr {f f' : G →* H} (hf : Continuous f) (hf' : Continuous f') (h : f = f')
    (x : CompletedGroupAlgebra Λ G) : map f hf x = map f' hf' x := by
  subst h
  rfl

/-- An isomorphism of topological groups is continuous as a homomorphism. -/
public theorem continuous_coe_monoidHom (e : G ≃ₜ* H) : Continuous (e : G →* H) :=
  e.continuous

/-- The ring isomorphism `Λ[[G]] ≃ Λ[[H]]` induced by an isomorphism of topological groups. -/
public def mapRingEquiv (e : G ≃ₜ* H) : CompletedGroupAlgebra Λ G ≃+* CompletedGroupAlgebra Λ H :=
  RingEquiv.ofRingHom (map (Λ := Λ) (e : G →* H) (continuous_coe_monoidHom e))
    (map (e.symm : H →* G) (continuous_coe_monoidHom e.symm))
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, map_map, RingHom.id_apply]
      refine (map_congr _ _ ?_ x).trans (map_id (Λ := Λ) x)
      exact MonoidHom.ext fun g => by simp)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, map_map, RingHom.id_apply]
      refine (map_congr _ _ ?_ x).trans (map_id (Λ := Λ) x)
      exact MonoidHom.ext fun g => by simp)

/-- The isomorphism induced by `e` is the map induced by `e`. -/
public theorem mapRingEquiv_apply (e : G ≃ₜ* H) (x : CompletedGroupAlgebra Λ G) :
    mapRingEquiv e x = map (e : G →* H) (continuous_coe_monoidHom e) x :=
  rfl

/-- The map induced by `f` preserves the augmentation. -/
public theorem augmentation_map [IsTopologicalGroup G] [IsTopologicalGroup H] (f : G →* H)
    (hf : Continuous f) (x : CompletedGroupAlgebra Λ G) :
    augmentation (map f hf x) = augmentation x := by
  rw [augmentation_eq (comapSubgroup f hf topSubgroup) x, augmentation_eq topSubgroup,
    eval_map f hf (map_mem_of_mem_comapSubgroup f hf topSubgroup)]
  have h : (finiteAugmentation (H ⧸ ((topSubgroup : OpenNormalSubgroup H) : Subgroup H))).comp
      (quotientMapAlgebra (Λ := Λ) f (map_mem_of_mem_comapSubgroup f hf topSubgroup)) =
      finiteAugmentation _ :=
    quotient_ringHom_ext fun g a => by
      rw [RingHom.comp_apply, quotientMapAlgebra_single, finiteAugmentation_single,
        finiteAugmentation_single]
  exact DFunLike.congr_fun h _

end CompletedGroupAlgebra

/-! ### Modules with an action trivial on an open normal subgroup -/

section Action

variable {Λ G} (M : Type w) [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
  [SMulCommClass G Λ M]

/-- The action of `G / U` on `M` by additive endomorphisms, for an open normal subgroup `U` acting
trivially. -/
public def quotientAction (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m) :
    G ⧸ (U : Subgroup G) →* AddMonoid.End M :=
  QuotientGroup.lift _ (DistribMulAction.toAddMonoidEnd G M) fun g hg => by
    ext m; exact hU g hg m

/-- The coset `gU` acts on `M` as `g`. -/
@[simp]
public theorem quotientAction_mk (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m)
    (g : G) (m : M) : quotientAction M U hU (g : G ⧸ (U : Subgroup G)) m = g • m :=
  rfl

/-- The action of `Λ[G/U]` on `M` by additive endomorphisms, for an open normal subgroup `U` acting
trivially. -/
public def quotientAlgebraAction (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) :
    MonoidAlgebra Λ (G ⧸ (U : Subgroup G)) →+* AddMonoid.End M :=
  liftNCRingHom (Module.toAddMonoidEnd Λ M) (quotientAction M U hU) fun a q => by
    induction q using QuotientGroup.induction_on with
    | H g => ext m; exact (smul_comm g a m).symm

/-- The element `δ_{gU} a` acts on `M` as `m ↦ a • g • m`. -/
@[simp]
public theorem quotientAlgebraAction_single (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) (g : G) (a : Λ) (m : M) :
    quotientAlgebraAction M U hU (single (g : G ⧸ (U : Subgroup G)) a) m = a • g • m := by
  simp [quotientAlgebraAction, liftNCRingHom, liftNC_single]
  rfl

/-- The actions of `Λ[G/U]` and `Λ[G/V]` on `M` are compatible with the transition map. -/
public theorem quotientAlgebraAction_comp {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) (hV : ∀ g ∈ V, ∀ m : M, g • m = m) :
    (quotientAlgebraAction M V hV).comp (quotientAlgebraMap Λ h) =
      quotientAlgebraAction M U hU :=
  CompletedGroupAlgebra.quotient_ringHom_ext fun g a => by ext m; simp

variable [IsTopologicalGroup G]

/-- The action of `Λ[[G]]` on a `Λ`-module with an action of `G` which is trivial on some open
normal subgroup: it is the action of `Λ[G/U]` for any such `U`. -/
public def CompletedGroupAlgebra.toAddMonoidEnd
    (hM : ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ m : M, g • m = m) :
    CompletedGroupAlgebra Λ G →+* AddMonoid.End M :=
  (quotientAlgebraAction M hM.choose hM.choose_spec).comp (CompletedGroupAlgebra.eval _)

omit [IsTopologicalGroup G] in
/-- The action of `Λ[[G]]` is computed by the action of `Λ[G/U]` for any open normal subgroup `U`
acting trivially. -/
public theorem CompletedGroupAlgebra.toAddMonoidEnd_eq
    (hM : ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ m : M, g • m = m) (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) (x : CompletedGroupAlgebra Λ G) :
    CompletedGroupAlgebra.toAddMonoidEnd M hM x =
      quotientAlgebraAction M U hU (CompletedGroupAlgebra.eval U x) := by
  have hW : ∀ g ∈ U ⊓ hM.choose, ∀ m : M, g • m = m := fun g hg => hU g hg.1
  rw [CompletedGroupAlgebra.toAddMonoidEnd, RingHom.comp_apply]
  exact (CompletedGroupAlgebra.apply_eval_eq_of_comp_eq
    ((quotientAlgebraAction_comp M inf_le_left hW hU).trans
      (quotientAlgebraAction_comp M inf_le_right hW hM.choose_spec).symm) x).symm

omit [IsTopologicalGroup G] in
/-- A group element `g` of `Λ[[G]]` acts on `M` as `g`. -/
@[simp]
public theorem CompletedGroupAlgebra.toAddMonoidEnd_of
    (hM : ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ m : M, g • m = m) (g : G) (m : M) :
    CompletedGroupAlgebra.toAddMonoidEnd M hM (CompletedGroupAlgebra.of (Λ := Λ) g) m = g • m := by
  simp [CompletedGroupAlgebra.toAddMonoidEnd]

omit [IsTopologicalGroup G] in
/-- The constant `a` of `Λ[[G]]` acts on `M` as `a`. -/
@[simp]
public theorem CompletedGroupAlgebra.toAddMonoidEnd_const
    (hM : ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ m : M, g • m = m) (a : Λ) (m : M) :
    CompletedGroupAlgebra.toAddMonoidEnd M hM (CompletedGroupAlgebra.const a) m = a • m := by
  simp [CompletedGroupAlgebra.toAddMonoidEnd, ← QuotientGroup.mk_one]

/-- A finite module with a continuous action of a compact group, that is, one whose point
stabilizers are open, is acted on trivially by some open normal subgroup. -/
public theorem exists_openNormalSubgroup_smul_eq [CompactSpace G] [Finite M]
    (hM : ∀ m : M, IsOpen {g : G | g • m = m}) :
    ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ m : M, g • m = m := by
  have hS : IsOpen ((⨅ m : M, MulAction.stabilizer G m : Subgroup G) : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hM
  obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    (⟨_, hS⟩ : OpenSubgroup G).isClopen (Subgroup.one_mem _)
  exact ⟨U, fun g hg => Subgroup.mem_iInf.1 (hU hg)⟩

end Action

end Stacks.GroupHomology

end

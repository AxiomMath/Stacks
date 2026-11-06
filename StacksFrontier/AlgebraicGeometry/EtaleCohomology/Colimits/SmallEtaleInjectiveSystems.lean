module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleDevissage

/-!
# [Stacks, Tag 0EXZ] for systems of abelian sheaves on the small étale sites

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes. Every system of abelian sheaves on the
small étale sites of its levels — a `Stacks.EtaleCohomology.EtaleSheafSystem`, [Stacks, Tag 0EZL]
— admits a levelwise monomorphism, compatible with the transitions, into a system whose sheaf at
every level is an injective object. That is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.hasPointwiseInjectiveEmbeddings`, and it
discharges `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasPointwiseInjectiveEmbeddings`, the
single remaining hypothesis of the dévissage
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage_of_mono_to_injective` and
hence of the dimension shift of [Stacks, Tag 09YQ].

## The construction

Choose at each level an injective sheaf `A_i` containing `F_i`, which exists because abelian
sheaves on a small étale site have enough injectives. The system is then

`G_i = A_i × ∏_{b : k ⟶ i} f_{b,*} A_k`,

the product over **all** arrows into `i` of the direct images of the chosen injectives, together
with **one extra factor** `A_i`. Each factor is injective — the direct image preserves injectives,
being right adjoint to the exact inverse image — so `G_i` is injective. The transition
`f_a^{-1} G_j ⟶ G_i` along `a : i ⟶ j` is given factorwise: on the factor indexed by `b : k ⟶ i`
it is the projection to `f_a^{-1} f_{b ≫ a,*} A_k` followed by the map
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction` adjoint to the comparison
`f_{b ≫ a,*} A_k ≅ f_{a,*} f_{b,*} A_k`, and on the extra factor it is the projection to
`f_a^{-1} f_{a,*} A_i` followed by the counit. The embedding `F_i ⟶ G_i` has the map adjoint to
`f_b^{-1}F_i ⟶ F_k ⟶ A_k` on the factor at `b`, and `F_i ⟶ A_i` on the extra factor.

## Why the extra factor is there

The source's product has no extra factor; its embedding is a monomorphism because the factor at
`b = 𝟙_i` is adjoint to `f_{𝟙}^{-1}F_i --F.map 𝟙--> F_i ⟶ A_i`, which is `F_i ⟶ A_i` once one
knows `F.map 𝟙 = 𝟙`. `Stacks.EtaleCohomology.EtaleSheafSystem` does **not** carry that law: the
source of [Stacks, Tag 0EZL] imposes the cocycle condition alone, and adding a `map_id` field
would weaken every theorem quantified over systems. Without it `F.map 𝟙` is only an idempotent and
that factor need not be a monomorphism — for `F_i = M` constant with all transitions `0` the whole
product embedding is `0`. The extra factor repairs exactly this: its component of the embedding is
`Injective.ι (F_i)`, a monomorphism outright, and the embedding is therefore a monomorphism because
it is so after one projection.

What the extra factor costs is one more coherence identity, namely that the counit is compatible
with the comparison of iterated inverse images,
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction_counit`. It is proved from
the same abstract lemma as the cocycle condition of the other factors, with the identity in place
of the composition comparison.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.hasPointwiseInjectiveEmbeddings` — [Stacks,
  Tag 0EXZ] for systems of abelian sheaves on the small étale sites of an inverse system of
  schemes.

## Implementation notes

The construction is carried out for an arbitrary coefficient category admitting the relevant
products, injective envelopes and inverse images, the abelian sheaves of the source being the
instance; only the final theorem is specific to `AddCommGrpCat.{u + 1}`, where the products come
from `UnivLE.{v, u + 1}` and the other two hypotheses from
`Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale_objectUniverse` and
`Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects`.

Both coherence identities — the cocycle condition of the product system and the counit identity —
are instances of `Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm`, the statement that
maps adjoint to a compatible family of comparisons of right adjoints satisfy the cocycle law. The
compatibility of the comparisons themselves is
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, the associativity pentagon of
the direct-image comparison, already available because `Stacks.EtaleCohomology.systemPushforward`
and `Stacks.EtaleCohomology.smallEtalePushforward` are the same functor and
`Stacks.EtaleCohomology.systemPushforwardComp D A a b` is
`Stacks.EtaleCohomology.smallEtalePushforwardComp'` at the named composite `D.map (a ≫ b)`. No
transport along `Category.assoc` is needed anywhere: the index is a preorder, so parallel arrows
of `Iᵒᵖ` are equal by proof irrelevance and `(c ≫ a) ≫ b` and `c ≫ a ≫ b` are the *same term*.

`UnivLE.{v, u + 1}` enters because the product is indexed by the arrows into a level, a family of
size `v`, while the coefficients are `AddCommGrpCat.{u + 1}`. It is already a hypothesis of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage` and of the dimension shift,
so the statement proved here is as strong as those consume; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleKaroubiColimit.lean` on why it is
not a restriction on the mathematics.

## References

* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)

Tags covered: none. Tag 0EXZ is registered in
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean` and in
`StacksFrontier/CategoryTheory/Sites/InverseSystem/InjectiveSystemsOnStrongSystems.lean`; this file is
its instance for the small étale sites, not a further occurrence of the tag.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I]

/-- The arrows of the index category with a fixed target: the set over which the product `G_i`
of the source's proof is taken. -/
private abbrev Incoming (i : Iᵒᵖ) := Σ k : Iᵒᵖ, k ⟶ i

variable (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- The factors of the product `G_i = A_i × ∏_{b : k ⟶ i} f_{b,*} A_k`: the direct image
`f_{β,*} A_k` at the arrow `β : k ⟶ i`, and the extra factor `A_i` at the new index. -/
private def incomingFactor (N : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A) (i : Iᵒᵖ) :
    Option (Incoming i) → Sheaf (smallEtaleTopology (D.obj i)) A
  | none => N i
  | some ⟨k, β⟩ => (systemPushforward D A β).obj (N k)

/-- The composite of the comparison of iterated inverse images with two transposed maps is the
transpose along `a ≫ b` of the corresponding composite, through the comparison of direct images. -/
private lemma pullbackComp_inv_map_homEquiv_symm {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {X : Sheaf (smallEtaleTopology (D.obj k)) A} {Y₁ : Sheaf (smallEtaleTopology (D.obj j)) A}
    {Y₂ : Sheaf (smallEtaleTopology (D.obj i)) A} (φ : X ⟶ (systemPushforward D A b).obj Y₁)
    (ψ : Y₁ ⟶ (systemPushforward D A a).obj Y₂) :
    (systemPullbackComp D A a b).inv.app X ≫
        (systemPullback D A a).map (((systemAdjunction D A b).homEquiv X Y₁).symm φ) ≫
          ((systemAdjunction D A a).homEquiv Y₁ Y₂).symm ψ =
      ((systemAdjunction D A (a ≫ b)).homEquiv X Y₂).symm
        (φ ≫ (systemPushforward D A b).map ψ ≫ (systemPushforwardComp D A a b).hom.app Y₂) :=
  leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A b) (systemAdjunction D A a)
    (systemAdjunction D A (a ≫ b)) (systemPushforwardComp D A a b) _ _

variable [∀ (i : Iᵒᵖ) (T : Type v),
    HasLimitsOfShape (Discrete T) (Sheaf (smallEtaleTopology (D.obj i)) A)]
  (N : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A)

attribute [local implicit_reducible] incomingFactor

/-- The sheaf `G_i = A_i × ∏_{b : k ⟶ i} f_{b,*} A_k` of the source's proof, with the extra
factor. -/
private abbrev productObject (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj i)) A :=
  ∏ᶜ incomingFactor D A N i

/-- The canonical map `f_a^{-1} f_{β ≫ a,*} A_k ⟶ f_{β,*} A_k` on the factor at `β : k ⟶ i`:
the map adjoint to the comparison `f_{β ≫ a,*} A_k ≅ f_{a,*} f_{β,*} A_k` of direct images. -/
private def incomingRestriction {i j : Iᵒᵖ} (a : i ⟶ j) {k : Iᵒᵖ} (β : k ⟶ i) :
    (systemPullback D A a).obj ((systemPushforward D A (β ≫ a)).obj (N k)) ⟶
      (systemPushforward D A β).obj (N k) :=
  ((systemAdjunction D A a).homEquiv _ _).symm
    ((systemPushforwardComp D A β a).inv.app (N k))

/-- The counit is the transpose of the identity. -/
private lemma homEquiv_symm_id {i j : Iᵒᵖ} (a : i ⟶ j)
    (X : Sheaf (smallEtaleTopology (D.obj i)) A) :
    ((systemAdjunction D A a).homEquiv ((systemPushforward D A a).obj X) X).symm
        (𝟙 ((systemPushforward D A a).obj X)) =
      (systemAdjunction D A a).counit.app X := by
  rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Transposing twice is the identity, read as a cancellation against the counit. -/
private lemma map_homEquiv_counit {i j : Iᵒᵖ} (a : i ⟶ j)
    {X : Sheaf (smallEtaleTopology (D.obj j)) A} {Y : Sheaf (smallEtaleTopology (D.obj i)) A}
    (g : (systemPullback D A a).obj X ⟶ Y) :
    (systemPullback D A a).map ((systemAdjunction D A a).homEquiv X Y g) ≫
        (systemAdjunction D A a).counit.app Y = g :=
  (Adjunction.homEquiv_counit ..).symm.trans (Equiv.symm_apply_apply _ g)

/-- Naturality of the adjunction bijection in the source, for the inverse image along a
transition. -/
private lemma map_comp_homEquiv_symm {i j : Iᵒᵖ} (a : i ⟶ j)
    {X X' : Sheaf (smallEtaleTopology (D.obj j)) A} {Y : Sheaf (smallEtaleTopology (D.obj i)) A}
    (f : X' ⟶ X) (g : X ⟶ (systemPushforward D A a).obj Y) :
    (systemPullback D A a).map f ≫ ((systemAdjunction D A a).homEquiv X Y).symm g =
      ((systemAdjunction D A a).homEquiv X' Y).symm (f ≫ g) :=
  ((systemAdjunction D A a).homEquiv_naturality_left_symm f g).symm

/-- Naturality of the adjunction bijection in the target, for the inverse image along a
transition. -/
private lemma homEquiv_symm_comp {i j : Iᵒᵖ} (a : i ⟶ j)
    {X : Sheaf (smallEtaleTopology (D.obj j)) A} {Y Y' : Sheaf (smallEtaleTopology (D.obj i)) A}
    (f : X ⟶ (systemPushforward D A a).obj Y) (g : Y ⟶ Y') :
    ((systemAdjunction D A a).homEquiv X Y').symm (f ≫ (systemPushforward D A a).map g) =
      ((systemAdjunction D A a).homEquiv X Y).symm f ≫ g :=
  (systemAdjunction D A a).homEquiv_naturality_right_symm f g

/-- Naturality of the comparison of iterated inverse images. -/
private lemma pullbackComp_inv_naturality {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {X Y : Sheaf (smallEtaleTopology (D.obj k)) A} (g : X ⟶ Y) :
    (systemPullbackComp D A a b).inv.app X ≫
        (systemPullback D A a).map ((systemPullback D A b).map g) =
      (systemPullback D A (a ≫ b)).map g ≫ (systemPullbackComp D A a b).inv.app Y := by
  simpa only [Functor.comp_map] using ((systemPullbackComp D A a b).inv.naturality g).symm

/-- `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.pullbackComp_inv_naturality` with a map
composed on the right, which is the form in which the cocycle computation uses it. -/
private lemma pullbackComp_inv_naturality_assoc {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {X Y : Sheaf (smallEtaleTopology (D.obj k)) A} (g : X ⟶ Y)
    {Z : Sheaf (smallEtaleTopology (D.obj i)) A}
    (h : (systemPullback D A a).obj ((systemPullback D A b).obj Y) ⟶ Z) :
    (systemPullbackComp D A a b).inv.app X ≫
        (systemPullback D A a).map ((systemPullback D A b).map g) ≫ h =
      (systemPullback D A (a ≫ b)).map g ≫ (systemPullbackComp D A a b).inv.app Y ≫ h :=
  (reassoc_of% pullbackComp_inv_naturality D A a b g) h

/-- **The cocycle condition on a single factor.** The restriction maps of the factor at
`γ : m ⟶ i` compose along `i ⟶ j ⟶ k` through the comparison of iterated inverse images. This is
the content of the cocycle condition of the product system at the factors indexed by arrows, and
it is the mate of the associativity pentagon of the direct-image comparison. -/
private lemma incomingRestriction_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) {m : Iᵒᵖ}
    (γ : m ⟶ i) :
    (systemPullbackComp D A a b).inv.app
        ((systemPushforward D A ((γ ≫ a) ≫ b)).obj (N m)) ≫
      (systemPullback D A a).map (incomingRestriction D A N b (γ ≫ a)) ≫
        incomingRestriction D A N a γ =
      incomingRestriction D A N (a ≫ b) γ := by
  refine (pullbackComp_inv_map_homEquiv_symm D A a b _ _).trans (congrArg _ ?_)
  rw [← Category.assoc]
  exact (smallEtalePushforwardComp'_inv_app_cocycle (D.map γ) (D.map a) (D.map b)
    (D.map (γ ≫ a)) (D.map_comp γ a) (D.map (a ≫ b)) (D.map_comp a b)
    (D.map ((γ ≫ a) ≫ b)) (D.map_comp (γ ≫ a) b) (D.map_comp γ (a ≫ b)) A (N m) =≫ _).trans <|
    (Category.assoc _ _ _).trans <|
      (_ ≫= (systemPushforwardComp D A a b).inv_hom_id_app _).trans (Category.comp_id _)

/-- **The cocycle condition on the extra factor.** The counit of the adjunction along `a ≫ b` is
the counit along `a` preceded by the restriction map of the factor at `a` and by the comparison of
iterated inverse images.

This is the one identity the extra factor costs, and it is the same computation as
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction_comp` with the identity in
place of the composition comparison. -/
private lemma incomingRestriction_counit {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp D A a b).inv.app ((systemPushforward D A (a ≫ b)).obj (N i)) ≫
      (systemPullback D A a).map (incomingRestriction D A N b a) ≫
        (systemAdjunction D A a).counit.app (N i) =
      (systemAdjunction D A (a ≫ b)).counit.app (N i) := by
  rw [← homEquiv_symm_id D A a (N i), ← homEquiv_symm_id D A (a ≫ b) (N i)]
  refine (pullbackComp_inv_map_homEquiv_symm D A a b _ _).trans (congrArg _ ?_)
  simp only [Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]

/-- The components of the transition `f_a^{-1} G_j ⟶ G_i`: on the factor at `β : k ⟶ i` the
projection to `f_a^{-1} f_{β ≫ a,*} A_k` followed by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction`, and on the extra factor the
projection to `f_a^{-1} f_{a,*} A_i` followed by the counit. -/
private def productTransitionComponent {i j : Iᵒᵖ} (a : i ⟶ j) :
    ∀ d : Option (Incoming i),
      (systemPullback D A a).obj (productObject D A N j) ⟶ incomingFactor D A N i d
  | none => (systemPullback D A a).map
        (Pi.π (incomingFactor D A N j) (some (⟨i, a⟩ : Incoming j))) ≫
      (systemAdjunction D A a).counit.app (N i)
  | some ⟨k, β⟩ => (systemPullback D A a).map
        (Pi.π (incomingFactor D A N j) (some (⟨k, β ≫ a⟩ : Incoming j))) ≫
      incomingRestriction D A N a β

private lemma productTransitionComponent_none {i j : Iᵒᵖ} (a : i ⟶ j) :
    productTransitionComponent D A N a none =
      (systemPullback D A a).map
          (Pi.π (incomingFactor D A N j) (some (⟨i, a⟩ : Incoming j))) ≫
        (systemAdjunction D A a).counit.app (N i) := rfl

private lemma productTransitionComponent_some {i j : Iᵒᵖ} (a : i ⟶ j) {m : Iᵒᵖ} (β : m ⟶ i) :
    productTransitionComponent D A N a (some ⟨m, β⟩) =
      (systemPullback D A a).map
          (Pi.π (incomingFactor D A N j) (some (⟨m, β ≫ a⟩ : Incoming j))) ≫
        incomingRestriction D A N a β := rfl

/-- The transition map `f_a^{-1} G_j ⟶ G_i` of the product system. -/
private def productTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D A a).obj (productObject D A N j) ⟶ productObject D A N i :=
  Pi.lift (productTransitionComponent D A N a)

private lemma productTransition_π {i j : Iᵒᵖ} (a : i ⟶ j) (d : Option (Incoming i)) :
    productTransition D A N a ≫ Pi.π (incomingFactor D A N i) d =
      productTransitionComponent D A N a d :=
  Pi.lift_comp_π _ _

/-- **The product system satisfies the cocycle condition of [Stacks, Tag 0EZL].** Factorwise this
is `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction_comp` at the factors
indexed by arrows and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.incomingRestriction_counit` at the extra
factor. -/
private lemma productTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp D A a b).inv.app (productObject D A N k) ≫
      (systemPullback D A a).map (productTransition D A N b) ≫ productTransition D A N a =
    productTransition D A N (a ≫ b) := by
  refine Pi.hom_ext _ _ fun d => ?_
  rcases d with _ | ⟨m, γ⟩ <;>
    simp only [Category.assoc, productTransition_π, productTransitionComponent_none,
      productTransitionComponent_some, ← Functor.map_comp_assoc] <;>
    rw [Functor.map_comp, Category.assoc, pullbackComp_inv_naturality_assoc] <;>
    dsimp only [incomingFactor]
  · rw [incomingRestriction_counit]
  · rw [incomingRestriction_comp]
    rfl

/-- The system `G` of the source's proof: at each level the product
`A_i × ∏_{b : k ⟶ i} f_{b,*} A_k`. -/
private def productSystem : EtaleSheafSystem D A where
  obj i := productObject D A N i
  map a := productTransition D A N a
  map_comp a b := productTransition_comp D A N a b

variable [∀ i : Iᵒᵖ, EnoughInjectives (Sheaf (smallEtaleTopology (D.obj i)) A)]
  (F : EtaleSheafSystem D A)

/-- A chosen injective sheaf containing the sheaf of the system at a level. -/
private def injectiveEnvelope (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj i)) A :=
  Injective.under (F.obj i)

attribute [local implicit_reducible] injectiveEnvelope

/-- The components of the embedding `F_i ⟶ G_i`: on the factor at `β : k ⟶ i` the map adjoint to
`f_β^{-1} F_i ⟶ F_k ⟶ A_k`, and on the extra factor the chosen monomorphism `F_i ⟶ A_i`. -/
private def envelopeComponent (i : Iᵒᵖ) : ∀ d : Option (Incoming i),
    F.obj i ⟶ incomingFactor D A (injectiveEnvelope D A F) i d
  | none => Injective.ι (F.obj i)
  | some ⟨k, β⟩ => (systemAdjunction D A β).homEquiv (F.obj i) (injectiveEnvelope D A F k)
      (F.map β ≫ Injective.ι (F.obj k))

/-- The component of the embedding at the extra factor is the chosen monomorphism. -/
private lemma envelopeComponent_none (i : Iᵒᵖ) :
    envelopeComponent D A F i none = Injective.ι (F.obj i) := rfl

/-- The component of the embedding at the factor indexed by an arrow. -/
private lemma envelopeComponent_some {i k : Iᵒᵖ} (β : k ⟶ i) :
    envelopeComponent D A F i (some ⟨k, β⟩) =
      (systemAdjunction D A β).homEquiv (F.obj i) (injectiveEnvelope D A F k)
        (F.map β ≫ Injective.ι (F.obj k)) := rfl

/-- The embedding `F_i ⟶ G_i` of the source's proof. -/
private def envelopeMap (i : Iᵒᵖ) :
    F.obj i ⟶ productObject D A (injectiveEnvelope D A F) i :=
  Pi.lift (envelopeComponent D A F i)

/-- The projections of the embedding are its components. -/
private lemma envelopeMap_π (i : Iᵒᵖ) (d : Option (Incoming i)) :
    envelopeMap D A F i ≫ Pi.π (incomingFactor D A (injectiveEnvelope D A F) i) d =
      envelopeComponent D A F i d :=
  Pi.lift_comp_π _ _

/-- The component of the embedding at the composite arrow `β ≫ a`, expressed through the
component at `β` and the transition along `a`. This is where the cocycle condition of `F` is
consumed. -/
private lemma envelopeComponent_some_comp {i j : Iᵒᵖ} (a : i ⟶ j) {k : Iᵒᵖ} (β : k ⟶ i) :
    envelopeComponent D A F j (some ⟨k, β ≫ a⟩) =
      (systemAdjunction D A a).homEquiv (F.obj j) (F.obj i) (F.map a) ≫
        (systemPushforward D A a).map (envelopeComponent D A F i (some ⟨k, β⟩)) ≫
          (systemPushforwardComp D A β a).hom.app (injectiveEnvelope D A F k) := by
  refine ((systemAdjunction D A (β ≫ a)).homEquiv (F.obj j)
      (injectiveEnvelope D A F k)).symm.injective ?_
  rw [envelopeComponent_some D A F (β ≫ a), Equiv.symm_apply_apply, ← F.map_comp β a,
    ← pullbackComp_inv_map_homEquiv_symm D A β a, Equiv.symm_apply_apply, envelopeComponent_some,
    Equiv.symm_apply_apply, Category.assoc, Category.assoc]

/-- **The embedding is compatible with the transitions**, so that it is a morphism of systems.
At the factor indexed by an arrow this is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.envelopeComponent_some_comp`; at the extra factor
it is the cancellation of the counit against the transpose. -/
private lemma envelopeMap_naturality {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D A a).map (envelopeMap D A F j) ≫
        productTransition D A (injectiveEnvelope D A F) a =
      F.map a ≫ envelopeMap D A F i := by
  refine Pi.hom_ext _ _ fun d => ?_
  rw [Category.assoc, productTransition_π, Category.assoc, envelopeMap_π]
  rcases d with _ | ⟨k, β⟩
  · rw [productTransitionComponent_none, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, envelopeMap_π, envelopeComponent_some,
      map_homEquiv_counit, envelopeComponent_none]
  · rw [productTransitionComponent_some, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, envelopeMap_π, envelopeComponent_some_comp,
      incomingRestriction]
    refine (map_comp_homEquiv_symm D A a _ _).trans ?_
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj, incomingFactor]
    rw [Category.comp_id]
    refine (homEquiv_symm_comp D A a _ _).trans ?_
    rw [Equiv.symm_apply_apply]

/-- **The embedding is a monomorphism.** Its projection to the extra factor is the chosen
monomorphism `F_i ⟶ A_i`, and a map with a monomorphic composite is a monomorphism. This is the
step the source gets from the identity law of its systems, which
`Stacks.EtaleCohomology.EtaleSheafSystem` does not have. -/
private lemma mono_envelopeMap (i : Iᵒᵖ) : Mono (envelopeMap D A F i) := by
  have : Mono (envelopeMap D A F i ≫
      Pi.π (incomingFactor D A (injectiveEnvelope D A F) i) none) := by
    rw [envelopeMap_π, envelopeComponent_none]; infer_instance
  exact mono_of_mono _ (Pi.π (incomingFactor D A (injectiveEnvelope D A F) i) none)

/-- **The product is injective** as soon as the chosen sheaves are: the direct image along a
transition preserves injective objects, and a product of injectives is injective. -/
private lemma injective_productObject
    [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).PreservesInjectiveObjects]
    (i : Iᵒᵖ) (hN : ∀ k : Iᵒᵖ, Injective (N k)) : Injective (productObject D A N i) := by
  have (d : Option (Incoming i)) : Injective (incomingFactor D A N i d) := by
    rcases d with _ | ⟨k, β⟩
    exacts [hN i, (systemPushforward D A β).injective_obj_of_injective (hN k)]
  infer_instance

variable [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- **[Stacks, Tag 0EXZ] on the small étale sites.** Every system of abelian sheaves on the small
étale sites of the levels of an inverse system of schemes admits a levelwise monomorphism,
compatible with the transitions, into a system whose sheaf at every level is an injective
object. -/
theorem hasPointwiseInjectiveEmbeddings [UnivLE.{v, u + 1}] :
    HasPointwiseInjectiveEmbeddings D := by
  have : ∀ (i j : Iᵒᵖ) (a : i ⟶ j),
      (systemPushforward D AddCommGrpCat.{u + 1} a).PreservesInjectiveObjects :=
    fun _ _ a => smallEtalePushforwardAb_preservesInjectiveObjects (D.map a)
  exact fun E => ⟨productSystem D _ (injectiveEnvelope D _ E), envelopeMap D _ E,
    envelopeMap_naturality D _ E, mono_envelopeMap D _ E,
    fun i => injective_productObject D _ _ i fun _ => Injective.injective_under _⟩

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end

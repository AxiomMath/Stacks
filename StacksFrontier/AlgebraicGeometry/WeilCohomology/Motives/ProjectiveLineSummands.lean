module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Category
public import StacksCore.Tactic.StacksAttribute

/-!
# The two summands of the motive of the projective line

Let `X = P¹_k` and let `x ∈ X` be a `k`-rational point. Example 0FG6 attaches to `x` the two
fibre classes `c₀ = [x × X]` and `c₂ = [X × x]` in `Corr⁰(X, X)`; they are orthogonal
idempotents summing to `[Δ] = 1`, so they cut the motive `h(X)` into two summands. This file
identifies both:

* `(X, c₀, 0) ≅ 1 = (Spec k, 1, 0)`;
* `(X, c₂, 0) ≅ 1(-1) = (Spec k, 1, -1)`.

The category `M_k` of Chow motives is the Karoubi envelope of the category of correspondences
(Stacks 0FGA), so a motive `(X, p, m)` is a formal direct factor and the source's description

  `Mor((Spec k, 1, -1), (X, c₂, 0)) = c₂ ∘ Corr¹(Spec k, X)`,

which its proof of part (2) explicitly recalls, is the morphism set of the Karoubi envelope —
`Stacks.WeilCohomology.CorrespondenceStructure.hom_motive_iff`. In that language both parts come
from one formal statement: a formal direct factor whose idempotent splits through an object of
the underlying category is isomorphic to that object. What distinguishes the two parts is how
the splitting is produced. For part (1) it is produced by the graph functor of Stacks 0FG3 out of
the two scheme morphisms of the source — the structure morphism `X → Spec k` and the rational
point `x : Spec k → X`, which satisfy `x ≫ (X → Spec k) = 1` — and part (1) is therefore proved
outright. For part (2) the two correspondences `a' ∈ Corr¹(Spec k, X)` and
`b' ∈ Corr^{-1}(X, Spec k)` are not graphs, and the source's two composition formulas for them
are intersection computations which this repository cannot state; they are carried as explicit
hypotheses.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.isoToKaroubi`: a formal direct factor whose idempotent
  splits through an object of the underlying category is isomorphic to that object.
* `Stacks.WeilCohomology.CorrespondenceStructure.constantGraphProjector`: the projector
  `c₀ = [x × X]`, the graph class of the constant morphism of `X` through `x`.
* `Stacks.WeilCohomology.CorrespondenceStructure.constantGraphMotive`: the motive
  `(X, c₀, 0)`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.idem_of_comp_eq_id`: the endomorphism attached to a
  retraction is idempotent.
* `Stacks.WeilCohomology.CorrespondenceStructure.constantGraphProjector_idem`: the source's
  composition rule `c₀ ∘ c₀ = c₀`, for `c₀` the graph class of the constant morphism.
* `Stacks.WeilCohomology.CorrespondenceStructure.constantGraphMotiveIso`: **Stacks 0FGD (1)**,
  `(X, c₀, 0) ≅ h(Spec k) = 1`.
* `CategoryTheory.Idempotents.Karoubi.exists_split_of_iso` and
  `Stacks.WeilCohomology.CorrespondenceStructure.exists_tateSplitting_of_iso`: those two
  composition formulas are recoverable from the conclusion of part (2).

## Implementation notes

**Where the statement lives, and where the Tate twist lives.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Category`, the ambient category `D` is the
opposite of the smooth projective schemes over `k` enlarged by the Tate twists, so that an object
of `D` is a pair `(X, m)`, a correspondence `S.Hom (X, m) (Y, n)` is an element of
`Corr^{n - m}(X, Y)`, and a scheme morphism `f : A → B` is a morphism `B ⟶ A` of `D`. Both parts
are therefore statements about objects of `D` and correspondences between them, with the degree
bookkeeping carried by `D`: in part (1) the two objects are `(Spec k, 0)` and `(X, 0)` and both
correspondences have degree `0`; in part (2) they are `T = (Spec k, -1)` and `(X, 0)`, so that

  `Hom(T, X) = Corr¹(Spec k, X)` and `Hom(X, T) = Corr^{-1}(X, Spec k)`

are exactly the two groups in which the source's `a'` and `b'` live. No motive, no category of
motives and no Tate twist is redefined here. The unit motive `1 = (Spec k, 1, 0)` is
`S.motiveFunctor.obj (𝟙_ D)`, the functor `h` of Stacks 0FGA at the monoidal unit of `D`, which
is `Spec k` by `Stacks.WeilCohomology.CorrespondenceStructure.tensorUnit_as`; part (1) is stated
for an arbitrary retract `P` of `Q` in `D` and specialises to the source's statement at
`P = 𝟙_ D`, `Q = X`.

**What part (1) proves, and what it recovers of Stacks 0FG6.** Part (1) assumes only
`α ≫ β = 𝟙 P` in `D` — for the source, that the rational point is a section of the structure
morphism — and uses nothing but functoriality of the graph, which is the conclusion of Stacks
0FG3 as carried by `Stacks.WeilCohomology.CorrespondenceStructure`. Nothing is granted. As a
by-product `Stacks.WeilCohomology.CorrespondenceStructure.constantGraphProjector_idem` proves the
composition rule `c₀ ∘ c₀ = c₀` of Example 0FG6, which
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.ProjectiveLineAlgebra` cannot state
because it has no composition of correspondences; there `c₀` is the class of the fibre `x × X`
and that is the same class, the fibre of a section being the graph of the constant morphism
through it, but the two live in different structures — one in the concrete rational Chow groups
of `X ×_S X`, the other in the abstract correspondence category which alone has composition — and
this repository carries no comparison between them.

**The carried hypotheses of part (2), and why they are irreducible here.** The source's proof of
part (2) performs two intersection computations: `[x] · [X] = [x]` on
`X = Spec k × X × Spec k`, which gives `b' ∘ a' = 1`, and
`pr₁₂^* b' · pr₂₃^* a' = X × Spec k × x` on `X × Spec k × X`, which gives `a' ∘ b' = c₂`. Both
speak about composition of correspondences, `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, which needs
the intersection product of Stacks 0FC1, the Gysin pullback of Stacks 0FFB and the projection
formula of Stacks 0FFC; none of the three is formalized in this repository, so neither formula
can be stated in that form here, let alone proved.

As with `Stacks.WeilCohomology.DiagonalPairingData` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Duality`, the honest statement is that with
only the categorical language available the hypothesis is inter-derivable with the conclusion:
`Stacks.WeilCohomology.CorrespondenceStructure.exists_tateSplitting_of_iso` produces the two
formulas back from the isomorphism. What is *not* assumed is the isomorphism itself, nor
idempotence of `c₂` beyond Example 0FG6's `c₂ ∘ c₂ = c₂`, which is what makes `(X, c₂, 0)` a
motive at all and is independent of any splitting; and the hypotheses are satisfiable, part (1)
being the same statement with the splitting supplied by graphs. What part (2) contributes over
the two formulas is the passage from them to an isomorphism *of motives*, that is the source's
step through `Mor((Spec k, 1, -1), (X, c₂, 0)) = c₂ ∘ Corr¹(Spec k, X)`.

**Abstraction over the geometry.** As throughout
`StacksDraft.AlgebraicGeometry.WeilCohomology.Correspondences`, neither smoothness, nor
projectivity, nor a base field, nor the projective line itself is imposed: the arguments use
none of them. Instantiating `D` by the opposite of the smooth projective schemes over `k`
enlarged by the Tate twists, `Q` by `P¹_k`, `P` by `Spec k` and `α`, `β` by the structure
morphism and the rational point recovers the statement of the source verbatim.

## References

* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents MonoidalCategory

universe v u w

namespace CategoryTheory.Idempotents.Karoubi

/-! ### Formal direct factors cut out by a split idempotent -/

section Split

variable {C : Type u} [Category.{v} C]

/-- The endomorphism attached to a retraction is idempotent: if `α ≫ β = 𝟙 P` then `β ≫ α` is an
idempotent endomorphism of `Q`, the projector onto `P` viewed as a retract of `Q`. -/
@[sga "4 VI 1.24.2" "partial"]
theorem idem_of_comp_eq_id {P Q : C} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) :
    (β ≫ α) ≫ (β ≫ α) = β ≫ α := by
  rw [Category.assoc, ← Category.assoc α, hαβ, Category.id_comp]

/-- A formal direct factor whose idempotent splits through an object of the underlying category
is isomorphic to that object. Given `α : P ⟶ M.X` and `β : M.X ⟶ P` with `α ≫ β = 𝟙 P` and
`β ≫ α = M.p`, the two underlying morphisms are already morphisms of the Karoubi envelope — each
is absorbed by the idempotents on either side — and they are mutually inverse there, the identity
of `M` being `M.p`. -/
def isoToKaroubi {P : C} {M : Karoubi C} (α : P ⟶ M.X) (β : M.X ⟶ P) (hαβ : α ≫ β = 𝟙 P)
    (hβα : β ≫ α = M.p) : M ≅ (toKaroubi C).obj P where
  hom := ⟨β, by
    change M.p ≫ β ≫ 𝟙 P = β
    rw [Category.comp_id, ← hβα, Category.assoc, hαβ, Category.comp_id]⟩
  inv := ⟨α, by
    change 𝟙 P ≫ α ≫ M.p = α
    rw [Category.id_comp, ← hβα, ← Category.assoc, hαβ, Category.id_comp]⟩
  hom_inv_id := by ext; exact hβα
  inv_hom_id := by ext; exact hαβ

@[simp]
theorem isoToKaroubi_hom_f {P : C} {M : Karoubi C} (α : P ⟶ M.X) (β : M.X ⟶ P)
    (hαβ : α ≫ β = 𝟙 P) (hβα : β ≫ α = M.p) : (isoToKaroubi α β hαβ hβα).hom.f = β :=
  rfl

@[simp]
theorem isoToKaroubi_inv_f {P : C} {M : Karoubi C} (α : P ⟶ M.X) (β : M.X ⟶ P)
    (hαβ : α ≫ β = 𝟙 P) (hβα : β ≫ α = M.p) : (isoToKaroubi α β hαβ hβα).inv.f = α :=
  rfl

/-- Conversely an isomorphism between a formal direct factor `M` and an object `P` of the
underlying category splits the idempotent of `M` through `P`: the two underlying morphisms of the
isomorphism are a retraction pair for it. So the hypotheses of
`CategoryTheory.Idempotents.Karoubi.isoToKaroubi` are recoverable from its conclusion. -/
theorem exists_split_of_iso {P : C} {M : Karoubi C} (e : M ≅ (toKaroubi C).obj P) :
    ∃ (α : P ⟶ M.X) (β : M.X ⟶ P), α ≫ β = 𝟙 P ∧ β ≫ α = M.p := by
  exact ⟨e.inv.f, e.hom.f, hom_ext_iff.mp e.inv_hom_id,
    hom_ext_iff.mp e.hom_inv_id⟩

end Split

end CategoryTheory.Idempotents.Karoubi

namespace Stacks.WeilCohomology

namespace CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
  (S : CorrespondenceStructure.{v, u, w} D)

/-! ### The summand cut out by the graph of a constant morphism -/

/-- The projector `c₀ = [x × X]` of Example 0FG6, as a self correspondence of `Q`: the graph
class `[Γ_{β ≫ α}]` of the composite `β ≫ α`.

For the source `Q` is `X = P¹_k`, `P` is `Spec k`, and — the ambient category being the opposite
of the smooth projective schemes over `k` — `α` is the structure morphism `X → Spec k` and `β`
the rational point `x : Spec k → X`, so that `β ≫ α` is the constant morphism `X → x → X` and
its graph is the fibre `x × X`. -/
def constantGraphProjector {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) :
    (Obj.mk Q : S.Obj) ⟶ Obj.mk Q :=
  S.graph (β ≫ α)

/-- The composition rule `c₀ ∘ c₀ = c₀` of Example 0FG6: the graph class of the constant
morphism through a section is idempotent, the graph of a composite being the composite of the
graphs. -/
theorem constantGraphProjector_idem {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) :
    S.constantGraphProjector α β ≫ S.constantGraphProjector α β =
      S.constantGraphProjector α β := by
  rw [constantGraphProjector, comp_eq, ← S.graph_comp, Karoubi.idem_of_comp_eq_id α β hαβ]

/-- The motive `(X, c₀, 0)` of Stacks 0FGD (1): the summand of `h(X)` cut out by the projector
`c₀ = [x × X]`, as an object of the Karoubi envelope of the category of correspondences. -/
abbrev constantGraphMotive {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) : S.Motive :=
  ⟨Obj.mk Q, S.constantGraphProjector α β, S.constantGraphProjector_idem α β hαβ⟩

/-- **Stacks Project, Tag 0FGD (1).** The motive `(X, c₀, 0)` is isomorphic to the motive
`h(Spec k) = 1 = (Spec k, 1, 0)`.

The graph classes of the structure morphism and of the rational point are the source's
`a ∈ Corr⁰(Spec k, X)` and `b ∈ Corr⁰(X, Spec k)`. Functoriality of the graph turns the identity
`x ≫ (X → Spec k) = 1` of the source into `b ∘ a = 1` and gives `a ∘ b = [Γ_{X → x → X}] = c₀`,
so `c₀` splits through `Spec k` and `a`, `b` are mutually inverse morphisms of motives. -/
@[stacks 0FGD "part (1): the motive (X, c_0, 0) is isomorphic to 1 = (Spec k, 1, 0)"]
def constantGraphMotiveIso {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) :
    S.constantGraphMotive α β hαβ ≅ S.motiveFunctor.obj P :=
  Karoubi.isoToKaroubi (P := Obj.mk P) (S.graph α) (S.graph β)
    (by rw [comp_eq, ← S.graph_comp, hαβ, S.graph_id]; exact (id_eq _).symm)
    (by rw [comp_eq, ← S.graph_comp]; rfl)

@[simp]
theorem constantGraphMotiveIso_hom_f {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) :
    (S.constantGraphMotiveIso α β hαβ).hom.f = S.graph β :=
  rfl

@[simp]
theorem constantGraphMotiveIso_inv_f {P Q : D} (α : P ⟶ Q) (β : Q ⟶ P) (hαβ : α ≫ β = 𝟙 P) :
    (S.constantGraphMotiveIso α β hαβ).inv.f = S.graph α :=
  rfl

/-! ### The summand cut out by the complementary projector -/

variable {T Q : D} (c₂ : (Obj.mk Q : S.Obj) ⟶ Obj.mk Q) (hc₂ : c₂ ≫ c₂ = c₂)

/-- The two composition formulas granted by
`Stacks.WeilCohomology.CorrespondenceStructure.tateProjectorMotiveIso` are recoverable from its
conclusion: an isomorphism `(X, c₂, 0) ≅ 1(-1)` has underlying correspondences `a'` and `b'` with
`b' ∘ a' = 1` and `a' ∘ b' = c₂`. So with only the categorical language available the carried
hypothesis of Stacks 0FGD (2) is inter-derivable with its conclusion, exactly as for
`Stacks.WeilCohomology.DiagonalPairingData` and Stacks 0FGI; narrowing it needs composition of
correspondences, that is Stacks 0FC1, 0FFB and 0FFC. -/
theorem exists_tateSplitting_of_iso
    (e : (⟨Obj.mk Q, c₂, hc₂⟩ : S.Motive) ≅ S.motiveFunctor.obj T) :
    ∃ (a : (Obj.mk T : S.Obj) ⟶ Obj.mk Q) (b : (Obj.mk Q : S.Obj) ⟶ Obj.mk T),
      a ≫ b = 𝟙 (Obj.mk T) ∧ b ≫ a = c₂ :=
  Karoubi.exists_split_of_iso (P := Obj.mk T) e

end CorrespondenceStructure

end Stacks.WeilCohomology

end

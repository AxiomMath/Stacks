module

public import Mathlib.Order.DirectedInverseSystem


import StacksFrontier.RingTheory.ColimitPresentation.Canonical
import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Category.Ring.Basic
import StacksCore.Tactic.EgaSgaAttribute


@[expose] public section

universe u

/-!
# Algebras of finite presentation are the finitely presentable objects

Proof of Stacks 00QO: for `S` an algebra over `R : CommRingCat`, the ring map `R → S` is of
finite presentation if and only if `S` is a finitely presentable object of the category
`Under R` of `R`-algebras, and already if and only if every `R`-algebra map from `S` to the
colimit of a directed system of `R`-algebras factors through a member of the system.

The implication (1) ⟹ (2) is Mathlib's `CommRingCat.isFinitelyPresentable_under`, whose proof
is the source's: an `R`-algebra map out of `R[x_1, …, x_n]/(f_1, …, f_m)` is a choice of images
of the `x_i` satisfying the relations `f_j`, and both the images and the vanishing of the
relations can be realized in a single member of a filtered system. The implication (2) ⟹ (3) is
the special case of a directed poset. For (3) ⟹ (1) the source writes `S = colim_λ S_λ` with
`S_λ` of finite presentation over `R` (Lemma 00QN) and factors the identity of `S` as
`S → S_λ → S`, which exhibits `S` as an `R`-algebra retract of `S_λ`; a retract of an algebra
of finite presentation is of finite presentation, by Lemma 00F4 parts (4) and (2).

## Main results

* `Stacks.AlgebraCategory.Presentability.solution`: the statement of Tag 00QO.

## Implementation notes

Lemma 00QN produces its colimit as a `DirectLimit` of `R`-algebras, whereas item (3) speaks of a
colimit cocone in `Under R`. The mathematics of the translation is one lemma,
`Stacks.AlgebraCategory.Presentability.isColimitDirectLimitCocone`: the direct limit of a directed
system of `R`-algebras, with its canonical maps `G l → colim_l G l`, is a colimit of the
corresponding diagram of rings, the universal property of the colimit being `DirectLimit.Ring.lift`
and its uniqueness clause being the induction principle `DirectLimit.induction`. The rest is
transport: a compatible family `g l : G l →ₐ[R] A` whose induced map `colim_l G l → A` is bijective
gives a cocone isomorphic to that one, and `CategoryTheory.Under.isColimitLiftCocone` moves a
colimit of the diagram of rings to a colimit in `Under R` — legitimately, a directed poset being
nonempty. The diagram in `Under R` is therefore Mathlib's `CategoryTheory.Under.lift` applied to
the diagram of rings and to the natural transformation given by the structure maps
`algebraMap R (G l)`.

The retract step is `Stacks.AlgebraCategory.Presentability.finitePresentation_of_retract`: an
`R`-algebra `A` admitting an `R`-algebra map `σ : A →ₐ[R] T` with a retraction `π : T →ₐ[R] A` is
of finite presentation as soon as `T` is. This is Algebra, Lemma 00F4 (4)
(`AlgHom.FinitePresentation.of_comp_finiteType`, which makes `π` of finite presentation, `σ` being
of finite type because `T` is) followed by (2) (`AlgHom.FinitePresentation.comp`, applied to `R → T
→ A`). Mathlib has the two ingredients but not the retract statement itself. The identifications of
`R → A` with `π ∘ (R → T)` and of `R → T` with `σ ∘ (R → A)` are instances of `Subsingleton (R
→ₐ[R] ·)`.

## References

* [StacksProject 00QO](https://stacks.math.columbia.edu/tag/00QO)
-/

open CategoryTheory Limits



namespace Stacks.AlgebraCategory.Presentability

noncomputable section DirectedSystem

variable {R : CommRingCat.{u}} {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ l, CommRing (G l)] [∀ l, Algebra ↑R (G l)]
    (f : ∀ i j, i ≤ j → G i →ₐ[↑R] G j) [DirectedSystem G fun i j h ↦ ⇑(f i j h)]

/-- The diagram in `CommRingCat` of a directed system `G` of `R`-algebras. -/
@[simps]
private def directLimitDiagram : Λ ⥤ CommRingCat.{u} where
  obj l := CommRingCat.of (G l)
  map {i j} h := CommRingCat.ofHom (f i j h.le).toRingHom
  map_id i := by ext x; exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(f i j h)) x
  map_comp {i j k} hij hjk := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(f i j h)) hij.le hjk.le x).symm

/-- The structure maps `R → G l` of a directed system of `R`-algebras, as a natural
transformation from the constant diagram, which is the datum lifting `directLimitDiagram`
to a diagram in `Under R`. -/
@[simps]
private def directLimitStructure :
    (Functor.const Λ).obj R ⟶ directLimitDiagram (R := R) G f where
  app l := CommRingCat.ofHom (algebraMap ↑R (G l))
  naturality i j h := by ext x; exact ((f i j h.le).commutes x).symm

variable {A : Type u} [CommRing A] [Algebra ↑R A] (g : ∀ l, G l →ₐ[↑R] A)
    (hg : ∀ i j h x, g j (f i j h x) = g i x)

/-- The cocone on `directLimitDiagram` with vertex `A` attached to a compatible family of
`R`-algebra maps `g l : G l →ₐ[R] A`. -/
@[simps]
private def coconeOfCompatible : Cocone (directLimitDiagram (R := R) G f) where
  pt := CommRingCat.of A
  ι :=
    { app l := CommRingCat.ofHom (g l).toRingHom
      naturality := fun i j h ↦ by ext x; exact hg i j h.le x }

/-- The direct limit of `G`, as a cocone on `directLimitDiagram` whose legs are the canonical
maps `G l → colim_l G l`. -/
private def directLimitCocone : Cocone (directLimitDiagram (R := R) G f) :=
  coconeOfCompatible G f (DirectLimit.Algebra.of G f) fun _ _ h x ↦ DirectLimit.Algebra.of_f h x

/-- **The direct limit of a directed system of `R`-algebras is a colimit of the corresponding
diagram of rings**: the universal property of `DirectLimit` is the universal property of the
colimit, and `DirectLimit.induction` is the uniqueness clause. -/
private def isColimitDirectLimitCocone : IsColimit (directLimitCocone G f) where
  desc t := CommRingCat.ofHom <| DirectLimit.Ring.lift G f ↑t.pt (fun l ↦ (t.ι.app l).hom)
    fun _ _ h x ↦ congr($(t.w (homOfLE h)).hom x)
  fac t l := by ext x; rfl
  uniq t m hm := by
    ext x
    induction x using DirectLimit.induction with | _ l y
    exact congr($(hm l).hom y)

/-- If the induced map `colim_l G l → A` is bijective, then `A` together with the family `g`
is a colimit of the diagram of rings `directLimitDiagram`: it is isomorphic, as a cocone, to the
direct limit. -/
private def isColimitCoconeOfCompatible
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G f A g hg)) :
    IsColimit (coconeOfCompatible G f g hg) :=
  (isColimitDirectLimitCocone G f).ofIsoColimit <| Cocone.ext
    (RingEquiv.ofBijective (DirectLimit.Algebra.lift G f A g hg).toRingHom hbij).toCommRingCatIso
    fun _ ↦ by ext x; rfl

/-- The same statement one level up: if the induced map `colim_l G l → A` is bijective, then `A`
is the colimit of the directed system `G` in the category `Under R` of `R`-algebras. -/
private def isColimitUnderCoconeOfCompatible
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G f A g hg)) :
    IsColimit (Under.liftCocone (directLimitDiagram (R := R) G f) (directLimitStructure G f)
      (coconeOfCompatible G f g hg) (CommRingCat.ofHom (algebraMap ↑R A))
      fun l ↦ by ext x; exact (g l).commutes x) :=
  Under.isColimitLiftCocone _ _ _ _ _ (isColimitCoconeOfCompatible G f g hg hbij)

end DirectedSystem

/-- **A retract of an algebra of finite presentation is of finite presentation.** If `σ : A → T`
is a map of `R`-algebras admitting an `R`-algebra retraction `π : T → A`, and `T` is of finite
presentation over `R`, then so is `A`. This is Algebra, Lemma 00F4 (4) followed by (2). -/
public theorem finitePresentation_of_retract {R A T : Type*} [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra R T] [Algebra.FinitePresentation R T]
    (σ : A →ₐ[R] T) (π : T →ₐ[R] A) (h : ∀ a, π (σ a) = a) :
    Algebra.FinitePresentation R A := by
  have hT : (Algebra.ofId R T).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr ‹_›
  have hσ : σ.FiniteType := AlgHom.FiniteType.of_comp_finiteType (f := Algebra.ofId R A) <| by
    rw [Subsingleton.elim (σ.comp (Algebra.ofId R A)) (Algebra.ofId R T)]
    exact AlgHom.FiniteType.of_finitePresentation hT
  have hπσ : π.comp σ = AlgHom.id R A := AlgHom.ext h
  have hπ : π.FinitePresentation := .of_comp_finiteType σ (hπσ ▸ .id R A) hσ
  have key : (Algebra.ofId R A).FinitePresentation :=
    Subsingleton.elim (π.comp (Algebra.ofId R T)) (Algebra.ofId R A) ▸ hπ.comp hT
  exact RingHom.finitePresentation_algebraMap.mp key

/-- **Lemma 00QO.** For an algebra `S` over `R : CommRingCat` the following are equivalent:
the ring map `R → S` is of finite presentation; `S` is a finitely presentable object of
`Under R`; every `R`-algebra map from `S` to the colimit of a directed system of `R`-algebras
factors through a member of the system. -/
public theorem solution {R : CommRingCat.{u}} (S : Under R) :
    List.TFAE
      [ S.hom.hom.FinitePresentation,
        IsFinitelyPresentable.{u} S,
        ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
          (A : Λ ⥤ Under R) (c : Cocone A), IsColimit c → ∀ g : S ⟶ c.pt,
            ∃ (l : Λ) (g' : S ⟶ A.obj l), g' ≫ c.ι.app l = g ] := by
  tfae_have 1 → 2 := fun h ↦ CommRingCat.isFinitelyPresentable_under R S h
  tfae_have 2 → 3 := by
    intro _ Λ _ _ _ A c hc g
    exact IsFinitelyPresentable.exists_hom_of_isColimit hc g
  tfae_have 3 → 1 := by
    intro h3
    let _ : Algebra ↑R ↑S.right := S.hom.hom.toAlgebra
    obtain ⟨Λ, _, _, _, G, _, _, f, _, g, hg, hFP, -, hbij⟩ :=
      Algebra.exists_directedSystem_finitePresentation_lift_bijective ↑R ↑S.right
    -- item (3) applied to the system of Lemma 00QN factors the identity of `S` through `G l`
    obtain ⟨l, σ, hσ⟩ := h3 Λ _ _ (isColimitUnderCoconeOfCompatible G f g hg hbij)
      (Under.homMk (𝟙 ↑S.right) (by ext x; rfl))
    have := hFP l
    let σ' : ↑S.right →ₐ[↑R] G l := ⟨σ.right.hom, fun x ↦ congr($(Under.w σ).hom x)⟩
    exact RingHom.finitePresentation_algebraMap.mpr <|
      finitePresentation_of_retract σ' (g l) fun x ↦ congr($(hσ).right.hom x)
  tfae_finish

end Stacks.AlgebraCategory.Presentability

/-!
# Algebras of finite presentation are the finitely presentable objects

Let `φ : R → S` be a ring map. The following are equivalent:

1. `φ` is of finite presentation;
2. for every directed system `A_λ` of `R`-algebras the canonical map
   `colim_λ Homᵣ(S, A_λ) → Homᵣ(S, colim_λ A_λ)` is bijective;
3. for the same systems that map is surjective.

So the `R`-algebras of finite presentation are exactly the "compact" objects of the category
of `R`-algebras: the ones whose covariant hom functor commutes with directed colimits.

## Main results

* `CommRingCat.isFinitelyPresentable_under_tfae`: the three conditions above, for
  `S : Under R` with `R : CommRingCat`, are equivalent.

## Implementation notes

The category of `R`-algebras is `Under R` for `R : CommRingCat`, in which the hom set from `S`
to `A` is `Homᵣ(S, A)`; a directed system of `R`-algebras is a functor `Λ ⥤ Under R` out of a
nonempty directed order, and `colim_λ A_λ` is any cocone `c` on it with `IsColimit c`, so the
comparison map is the canonical one and no choice of construction of the colimit is made.

Condition (2), "`colim_λ Homᵣ(S, -)  → Homᵣ(S, colim_λ -)` is bijective", is Mathlib's
`CategoryTheory.IsFinitelyPresentable S`: by
`isFinitelyPresentable_iff_preservesFilteredColimits` it says exactly that
`coyoneda.obj (op S)` preserves the relevant colimits, and a map of sets is bijective iff it is
an isomorphism. Condition (3) is spelled out, as the factorisation property
`∃ l, ∃ g' : S ⟶ A l, g' ≫ c.ι.app l = g`, because surjectivity of the comparison map is what
that property says and Mathlib names no half-preservation class; it is the conclusion
of `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`.

The two departures from the source's form both strengthen the statement, and are the only
ones. First, (2) is taken over *all* filtered index categories rather than only directed
orders: that is how `IsFinitelyPresentable` is defined, it is what Mathlib proves in
`CommRingCat.isFinitelyPresentable_under`, and by Categories, Lemma `0032` the two agree.
Second, (3) is taken over *partially* ordered directed index sets rather than preordered ones,
which is fewer systems and hence a weaker condition: this is the form Lemma `00QN` produces,
and in an equivalence a weaker item is a stronger theorem. Together the result reads: bijective
for every filtered diagram as soon as it is surjective for every directed poset of algebras.

Faithfulness. (1) There is no hypothesis besides the ring map `S.hom` itself, which all three
items mention; the conditions are the three equivalent statements, not one of them with the
others as decoration. (2) The scalars and base are the source's: the index category is
`Λ ⥤ Under R`, so every algebra, transition map and comparison map is over `R`, and `S ⟶ A l`
in `Under R` is `Homᵣ(S, A l)`, not a plain ring map. (3) The canonical map of the source is
pinned, not merely asserted to exist: (2) is preservation of the colimit by `coyoneda.obj
(op S)`, whose comparison map is the canonical one, and (3) factors the given `g : S ⟶ c.pt`
through the given cocone leg `c.ι.app l`. (4) The instantiation is not degenerate: for
`S = R[x₁, x₂, x₃, …]` on countably many variables item (1) fails, and item (3) fails too,
because `S` is the colimit of the directed system `R[x₁, …, xₙ]` in which the identity of `S`
factors through no member; while for `S` of finite presentation all three hold, so no item is
vacuous or trivially true.

## References

* [StacksProject 00QO](https://stacks.math.columbia.edu/tag/00QO)

## Tags

finite presentation, finitely presentable object, compact object, directed colimit
-/

open CategoryTheory Limits



namespace CommRingCat

/-- **Algebras of finite presentation are the finitely presentable objects.** For an
`R`-algebra `S`, the following are equivalent: `S` is of finite presentation over `R`; `S` is a
finitely presentable object of the category `Under R` of `R`-algebras, that is
`colim_λ Homᵣ(S, A_λ) → Homᵣ(S, colim_λ A_λ)` is bijective for every filtered system of
`R`-algebras; and every `R`-algebra map from `S` to the colimit of a directed system of
`R`-algebras factors through one of its members, that is the same comparison map is
merely surjective. -/
@[stacks 00QO "Item (2) is `IsFinitelyPresentable` in `Under R`, which is bijectivity of
`colim Homᵣ(S, A_λ) → Homᵣ(S, colim A_λ)` for every *filtered* system (Lemma `0032` identifies
these with directed ones); item (3) is the surjectivity of that map, spelled as factoring a
map through a member of the system, for every *partially* ordered directed system, the form
Lemma `00QN` provides. Both departures strengthen the equivalence. See the module docstring.",
  ega
  "IV 8.14.2.2" "more general",
  ega "IV 8.8.2.3" "f.p. => bijective",
  ega "IV 8.8.2.1" "f.p. case: bijective",
  ega "IV 8.13.1" "affine case, bijective",
  ega "IV 8.14.2" "X, S affine", ega "IV 8.14.2.2" "more general"]
public theorem isFinitelyPresentable_under_tfae {R : CommRingCat.{u}} (S : Under R) :
    List.TFAE
      [ S.hom.hom.FinitePresentation,
        IsFinitelyPresentable.{u} S,
        ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
          (A : Λ ⥤ Under R) (c : Cocone A), IsColimit c → ∀ g : S ⟶ c.pt,
            ∃ (l : Λ) (g' : S ⟶ A.obj l), g' ≫ c.ι.app l = g ] :=
    by apply Stacks.AlgebraCategory.Presentability.solution

end CommRingCat

/-!
# A criterion for an algebra to be a filtered colimit of algebras of a given family

Proof of Stacks 07C3. Let `R → Λ` be a ring map and let `E` be a family of `R`-algebras each
of which is of finite presentation over `R`. Then `Λ` is a filtered colimit of members of `E`
if and only if every `R`-algebra map `A → Λ` with `A` of finite presentation over `R` factors
as `A → B → Λ` with `B` in `E`.

## Main results

* `Stacks.AlgebraCategory.IndFactorization.solution`: the equivalence above.

## Implementation notes

Mathlib proves the equivalence in the generality of an arbitrary finitely accessible category,
as `CategoryTheory.ObjectProperty.ind_iff_exists`, with the categorical `IsFinitelyPresentable`
in place of finite presentation of a ring map: exactly the source's argument, the factorization
property being what makes the canonical diagram of `E`-objects over `Λ` final in the category
of all finitely presentable objects over `Λ` and hence filtered with colimit `Λ`. So what this
file supplies is the two ring-theoretic inputs that instantiate it at the category `Under R` of
`R`-algebras.

The first is Lemma `00QO`: an object of `Under R` is finitely presentable in the categorical
sense if and only if its structure map is of finite presentation. Mathlib has only the
implication `CommRingCat.isFinitelyPresentable_under`.

The second is that `Under R` is a finitely accessible category; Mathlib has no
`IsFinitelyAccessibleCategory` instance for any concrete category. It is
`CategoryTheory.IsCardinalFilteredGenerator.of_isDense_ι` at `ℵ₀` for the property of being of
finite presentation over `R`, and of the three hypotheses of that lemma two are Lemma `0BUF` —
over every `R`-algebra `A` the finitely presented `R`-algebras over `A` form a filtered category
whose canonical colimit is `A` — while the third, essential smallness of the family, is supplied
neither by Mathlib nor by the Stacks Project and so is proved here.

That smallness is really a statement about finite generation: an `R`-algebra of finite type is a
quotient of some `MvPolynomial (Fin n) R`, hence isomorphic to a member of the small skeleton
`FGAlgCatSkeleton R`. So it is proved in that generality and specialised by
`CategoryTheory.ObjectProperty.EssentiallySmall.of_le`. Mathlib has the same statement for
properties of bare rings, as `CommRingCat.essentiallySmall_of_finiteType`, but not for
`R`-algebras.

Two departures from the source's form are inherited from the statement, and both strengthen
it: the family `E` is an arbitrary `ObjectProperty (Under R)` rather than a set, the source's
smallness assumption being only a device to keep its index category small, and the equivalence
is an `Iff` rather than a two-item `List.TFAE`.

## References

* [StacksProject 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [StacksProject 00QO](https://stacks.math.columbia.edu/tag/00QO)
* [StacksProject 0BUF](https://stacks.math.columbia.edu/tag/0BUF)
-/

open CategoryTheory Cardinal

attribute [local instance] Cardinal.fact_isRegular_aleph0



namespace Stacks.AlgebraCategory.IndFactorization

/-- **Lemma 00QO.** An `R`-algebra is a finitely presentable object of the category of
`R`-algebras if and only if it is of finite presentation over `R`. -/
private lemma isFinitelyPresentable_under_iff {R : CommRingCat.{u}} (S : Under R) :
    IsFinitelyPresentable.{u} S ↔ S.hom.hom.FinitePresentation :=
  (CommRingCat.isFinitelyPresentable_under_tfae S).out 2 1

/-- The `R`-algebras of finite type over `R` are essentially small: such an algebra is a
quotient of some `MvPolynomial (Fin n) R`, hence isomorphic as an `R`-algebra to a member of
the small skeleton `FGAlgCatSkeleton R` of finitely generated `R`-algebras. -/
@[ega "IV 18.6.1" "partial"]
lemma essentiallySmall_finiteType (R : CommRingCat.{u}) :
    ObjectProperty.EssentiallySmall.{u} (fun B : Under R ↦ B.hom.hom.FiniteType) := by
  refine ⟨ObjectProperty.ofObj (fun T : FGAlgCatSkeleton R ↦
    Under.mk (CommRingCat.ofHom (algebraMap R (CommRingCat.of T.eval.obj)))), inferInstance, ?_⟩
  intro B hB
  obtain ⟨T, e, he⟩ := hB.exists_smallRepr
  refine ⟨_, ⟨T⟩, ⟨Under.isoMk (RingEquiv.toCommRingCatIso e.symm) ?_⟩⟩
  ext x
  simp [he]

/-- The category `Under R` of `R`-algebras is finitely accessible: it has filtered colimits,
and the `R`-algebras of finite presentation over `R` form an essentially small family of
finitely presentable objects which generates `Under R` under filtered colimits.

This is Lemma `0BUF` for the density and filteredness, Lemma `00QO` for the presentability, and
`essentiallySmall_finiteType` for the smallness. -/
private lemma isFinitelyAccessibleCategory_under (R : CommRingCat.{u}) :
    IsFinitelyAccessibleCategory.{u} (Under R) := by
  have : ObjectProperty.EssentiallySmall.{u}
      (fun B : Under R ↦ B.hom.hom.FinitePresentation) :=
    have := essentiallySmall_finiteType R
    .of_le fun _ ↦ RingHom.FiniteType.of_finitePresentation
  have hBUF :=
    CommRingCat.isFiltered_costructuredArrow_and_isDenseAt_finitePresentation (R := R)
  have : (ObjectProperty.ι fun B : Under R ↦ B.hom.hom.FinitePresentation).IsDense :=
    ⟨fun A ↦ (hBUF A).2⟩
  have (A : Under R) : IsCardinalFiltered (CostructuredArrow
      (ObjectProperty.ι fun B : Under R ↦ B.hom.hom.FinitePresentation) A) ℵ₀ :=
    (isCardinalFiltered_aleph0_iff _).2 (hBUF A).1
  have hle : (fun B : Under R ↦ B.hom.hom.FinitePresentation) ≤
      isCardinalPresentable (Under R) ℵ₀ := by
    rw [← ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
    exact fun B hB ↦ (isFinitelyPresentable_under_iff B).2 hB
  exact { toHasCardinalFilteredGenerator :=
    (IsCardinalFilteredGenerator.of_isDense_ι _ ℵ₀ hle).hasCardinalFilteredGenerator }

/-- **Lemma 07C3.** Let `E` be a family of `R`-algebras of finite presentation over `R`. An
`R`-algebra `Λ` is a filtered colimit of members of `E` if and only if every `R`-algebra map
`A → Λ` with `A` of finite presentation over `R` factors as `A → B → Λ` with `B` in `E`. -/
public theorem solution {R : CommRingCat.{u}} (Λ : Under R)
    {E : ObjectProperty (Under R)} (hE : E ≤ fun B : Under R ↦ B.hom.hom.FinitePresentation) :
    ObjectProperty.ind.{u} E Λ ↔
      ∀ A : Under R, A.hom.hom.FinitePresentation → ∀ f : A ⟶ Λ,
        ∃ (B : Under R) (g : A ⟶ B) (h : B ⟶ Λ), g ≫ h = f ∧ E B := by
  have := isFinitelyAccessibleCategory_under R
  rw [ObjectProperty.ind_iff_exists (P := E)
    fun B hB ↦ (isFinitelyPresentable_under_iff B).2 (hE B hB)]
  exact ⟨fun h A hA f ↦ @h A f ((isFinitelyPresentable_under_iff A).2 hA),
    fun h _ g hZ ↦ h _ ((isFinitelyPresentable_under_iff _).1 hZ) g⟩

end Stacks.AlgebraCategory.IndFactorization

/-!
# A criterion for an algebra to be a filtered colimit of algebras of a given family

Let `R → Λ` be a ring map and let `𝓔` be a family of `R`-algebras each of which is of finite
presentation over `R`. Then the following are equivalent:

1. `Λ` is a filtered colimit of members of `𝓔`;
2. every `R`-algebra map `A → Λ` with `A` of finite presentation over `R` admits a
   factorization `A → B → Λ` with `B ∈ 𝓔`.

The implication 1 ⟹ 2 is the compactness of a finitely presented algebra: a map from `A` into a
filtered colimit factors through a member of the diagram. For 2 ⟹ 1 one takes the *canonical*
diagram, the category `𝓙` of all `R`-algebra maps `B → Λ` with `B ∈ 𝓔`: the factorization
property says exactly that `𝓙` is cofinal in the category of all finitely presented `R`-algebras
over `Λ`, which is filtered with colimit `Λ`, so `𝓙` is filtered too and `Λ` is already the
colimit over `𝓙`.

## Main results

* `CommRingCat.ind_under_iff_exists_factorization`: the equivalence above, for a family `E` of
  objects of the category `Under R` of `R`-algebras.

## Implementation notes

The category of `R`-algebras is `Under R` for `R : CommRingCat`, in which an object `B` carries
the structure map `B.hom` and `A ⟶ B` is an `R`-algebra map; the source's *set* `𝓔` of
`R`-algebras is an `E : ObjectProperty (Under R)`, membership `B ∈ 𝓔` being `E B`, and "of
finite presentation over `R`" is the ring-theoretic `B.hom.hom.FinitePresentation`, as in
Lemmas `0BUF` and `00QO`.

Statement 1 is Mathlib's `CategoryTheory.ObjectProperty.ind.{u} E Λ`: there is a small filtered
category `J` and a colimit presentation of `Λ` by a diagram `J ⥤ Under R` all of whose values
satisfy `E`. So the colimit is a colimit of `R`-algebras, it is presented by a cocone together
with the assertion that this cocone is colimiting, and no construction of the colimit is chosen.

Two departures from the source's form, both strengthenings. First, `𝓔` is an arbitrary class
of objects rather than a set: the source assumes a set only to keep its index category small,
and no smallness hypothesis is needed, because the canonical index category
`CostructuredArrow E.ι Λ` is cofinal in the essentially small category of finitely presented
`R`-algebras over `Λ`, hence essentially small itself. Second, the equivalence is stated as an
`Iff` rather than a two-item `List.TFAE`, which is the same statement in Mathlib's spelling for
two items.

Mathlib proves this equivalence for any finitely accessible category, as
`CategoryTheory.ObjectProperty.ind_iff_exists`, with `IsFinitelyPresentable` in place of finite
presentation of a ring map. What is specific to `R`-algebras here, and is not in Mathlib, is
that the category of `R`-algebras is finitely accessible with the finitely presented
`R`-algebras as its finitely presentable objects: that is Lemma `0BUF` together with
Lemma `00QO` (of which Mathlib has the direction
`CommRingCat.isFinitelyPresentable_under`).

Faithfulness. (1) Every hypothesis is used: `hE` is what makes the canonical diagram of
`E`-objects over `Λ` filtered and cofinal, so it is needed for 2 ⟹ 1, while `Λ` and `E` occur on
both sides; there is no hypothesis the conclusion ignores. (2) The scalars and the base are the
source's: both sides are statements in `Under R`, so every algebra is an `R`-algebra, every map
an `R`-algebra map, and the colimit in statement 1 is a colimit of `R`-algebras rather than of
rings or of sets. (3) The maps are pinned rather than merely asserted to exist: statement 1
gives a cocone on the diagram with tip `Λ` and the assertion that it is colimiting, so the
comparison map `colim Bᵢ → Λ` is the one induced by the structure maps, and statement 2 factors
the *given* map `f` as `g ≫ h = f`. (4) The instantiation is not degenerate: for `E` the class
of all finitely presented `R`-algebras both sides hold for every `Λ` (Lemma `0BUF`), whereas for
`E` the class `{R}` and `Λ = R[x]` both sides fail, since the identity of `R[x]` factors through
no `R`-algebra map `R[x] → R`; so neither side is vacuous nor automatic.

## References

* [StacksProject 07C3](https://stacks.math.columbia.edu/tag/07C3)

## Tags

filtered colimit, finite presentation, ind-object, factorization
-/

open CategoryTheory Limits



namespace CommRingCat

/-- **Criterion for being a filtered colimit of algebras of a given family.** Let `R → Λ` be a
ring map and let `E` be a family of `R`-algebras of finite presentation over `R`. Then `Λ` is a
filtered colimit of members of `E` if and only if every `R`-algebra map `A → Λ` with `A` of
finite presentation over `R` factors as `A → B → Λ` with `B` in `E`. -/
@[stacks 07C3 "The family `𝓔` is an `E : ObjectProperty (Under R)` on the category `Under R` of
`R`-algebras, and \"`Λ` is a filtered colimit of members of `𝓔`\" is Mathlib's
`ObjectProperty.ind.{u} E Λ`. `E` is not assumed small; the source's set-theoretic hypothesis is
only a smallness device. See the module docstring."]
public theorem ind_under_iff_exists_factorization {R : CommRingCat.{u}} (Λ : Under R)
    {E : ObjectProperty (Under R)} (hE : E ≤ fun B : Under R ↦ B.hom.hom.FinitePresentation) :
    ObjectProperty.ind.{u} E Λ ↔
      ∀ A : Under R, A.hom.hom.FinitePresentation → ∀ f : A ⟶ Λ,
        ∃ (B : Under R) (g : A ⟶ B) (h : B ⟶ Λ), g ≫ h = f ∧ E B :=
    by exact Stacks.AlgebraCategory.IndFactorization.solution Λ hE

end CommRingCat

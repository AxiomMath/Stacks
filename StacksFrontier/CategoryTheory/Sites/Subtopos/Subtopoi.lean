module
public import StacksFrontier.CategoryTheory.Sites.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Closed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Open
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When the localization of a topos at a sheaf is a subtopos

Let `E` be a topos and let `F` be an object of `E`; in Stacks 08LW the topos is `E = Sh(C)` for a
site `C` and `F` is a sheaf on `C`. The localization of `E` at `F` is the slice category `E/F`,
and it carries the localization morphism of topoi `j_F : E/F ⟶ E` of Stacks 04GZ, whose inverse
image is `j_F⁻¹ = (H ↦ H × F / F)` and whose pushforward `j_{F,*}` is a right adjoint of it.

Stacks 08LW says that `F` is a subobject of the final object of `E` if and only if `E/F` is a
subtopos of `E`. A subtopos (Stacks 08LV) is a strictly full subcategory of `E` which is the
essential image of the pushforward of an embedding of topoi, an embedding being a morphism of
topoi whose pushforward is fully faithful (Stacks 08LU); the embedding presenting `E/F` is `j_F`
itself. So the mathematical content of the lemma is that `j_{F,*}` is fully faithful precisely
when any two morphisms of `E` into `F` agree.

Both conditions are also equivalent to `j_{F!} = Over.forget F` being fully faithful, which is
what makes this a statement about arbitrary `E`: the three functors form an adjoint triple
`j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}` (Stacks 04GZ (2)), the outer two members of an adjoint triple are fully
faithful together, and `Over.forget F` is full exactly when `F` is subterminal — no exactness
hypothesis on `E` and no property of the site take part.

## Main results

* `MorphismOfTopoi.isEmbedding_overLocalization_iff_isSubterminal` (Stacks 08LW): the
  localization morphism `j_F : E/F ⟶ E` is an embedding of topoi, i.e. `E/F` is the subtopos
  `j_{F,*}(E/F)` of `E`, if and only if `F` is a subobject of the final object of `E`.

## Implementation notes

Departures from the form of the source, none of them weakenings.

* `E` is an arbitrary cartesian monoidal category rather than `Sh(C)`, which is the generality of
  `MorphismOfTopoi.overLocalization` (Stacks 04GZ) in this library: binary products and a final
  object are all that `j_F⁻¹` needs, and the equivalence uses nothing else. The source's case is
  `E = Sheaf J (Type max u v)`.
* The pushforward `j_{F,*}` is taken as data — an arbitrary right adjoint `p` of `j_F⁻¹`, as in
  Stacks 04GZ, 04H0 and 04IR — because a cartesian monoidal category need not have one. In a
  topos it does: `F` is exponentiable, and pullbacks being available, `p` may be taken to be the
  functor of sections `CategoryTheory.Over.sections F`, with
  `adj = CategoryTheory.Over.toOverSectionsAdj F`. Nothing depends on the choice, `Full` and
  `Faithful` being invariant under natural isomorphism.
* Condition (2), "`E/F` is a subtopos of `E`", is read as "`j_F` is an embedding of topoi", which
  is how the source's own proof reads it: its proof of (2) ⇒ (1) opens "Assume (2). This means
  that `j_U^{-1}j_{U,*}G → G` is an isomorphism for all sheaves `G` on `C/U`", i.e. that the
  counit of `j_U^{-1} ⊣ j_{U,*}` is invertible, which by
  `MorphismOfTopoi.isEmbedding_iff_isIso_counit_app` is exactly `j_U` being an embedding.
  The alternative reading — that the essential image of `j_{F,*}` merely *be* a subtopos in the
  sense of Stacks 08LV, i.e. be the essential image of the pushforward of some embedding — makes
  the lemma false, so it cannot be meant: for `C` the one-point site, `E = Sh(C)` is the category
  of sets, `E/F ≌ Set × Set` for a two-element set `F`, and `j_{F,*}(A, B) = A × B`, whose
  essential image is all of `E` because `A ≅ A × 1`; that is the essential image of the identity
  embedding, hence a subtopos, while `F` is not a subobject of the final object.
* Consequently `IsSubtopos` (Stacks 08LV) does not appear here. It also could
  not: it asks for a *site* `D` with an embedding out of `Sh(D)`, and that `E/F` is again a
  category of sheaves on a site is the one assertion of Stacks 04GZ this library does not have
  (the source obtains it from Stacks 03CI and 00Y1). Given that equivalence,
  `isSubtopos_essImage_pushforward` turns the left-hand side below into the literal statement
  that `j_{F,*}`'s essential image is a subtopos.
* "`F` is a subobject of the final object" is `CategoryTheory.IsSubterminal F`, i.e. any two
  morphisms into `F` are equal; it is equivalent to the unique morphism `F ⟶ ⊤` being a
  monomorphism (`CategoryTheory.IsSubterminal.mono_terminal_from` and
  `CategoryTheory.isSubterminal_of_mono_terminal_from`) but does not mention a chosen final
  object. Stacks 00Y2, the source's input for (1) ⇒ (2), uses the same spelling for the same
  condition on an object of the site.

Faithfulness.

1. Every hypothesis is used: `adj` is what makes `j_F` a morphism of topoi at all and is what the
   conclusion is about, and the cartesian monoidal structure is what makes `j_F⁻¹` exist; there is
   no hypothesis on the site, on `F`, or on exactness, the source having none either.
2. The base is the source's: the topos is the ambient category `E` throughout, `E/F` is its slice
   at `F`, and the morphism compared is the localization morphism of `E` at `F`, not a morphism of
   sheaves on a localized site.
3. The morphism the source names is pinned, not merely asserted to exist: `j_F` is
   `MorphismOfTopoi.overLocalization F adj`, whose inverse image is `toOver F` on the nose
   (Stacks 04GZ (1)) and whose lower shriek is `Over.forget F` (Stacks 04GZ (2)); the condition is
   full faithfulness of *its* pushforward.
4. Not degenerate: with `E = Sheaf J (Type max u v)` and `F = ⊤` both sides hold, `Over ⊤ ≌ E`;
   with `E` the category of sets and `F` a two-element set both sides fail, by the computation
   above. So neither side is vacuous or automatic.

## References

Stacks Project, tag 08LW (`sites-lemma-open-subtopos`); Stacks 08LX defines an *open* subtopos to
be one of the subtopoi produced here, and Stacks 08LY constructs its closed complement.
-/

namespace CategoryTheory.Sites.Subtopos

section

universe v u
open CategoryTheory

namespace Stacks.Subtopos.SubterminalCriterion

@[expose] public section

/-- A functor is full and faithful if and only if it admits a `Functor.FullyFaithful` structure;
the two spellings of full faithfulness agree.  Companion of
`CategoryTheory.Functor.FullyFaithful.nonempty_iff_map_bijective`. -/
private lemma nonempty_fullyFaithful_iff_full_and_faithful {C : Type*} [Category C] {D : Type*}
    [Category D] (G : C ⥤ D) : Nonempty G.FullyFaithful ↔ G.Full ∧ G.Faithful :=
  ⟨fun ⟨h⟩ => ⟨h.full, h.faithful⟩, fun ⟨_, _⟩ => ⟨.ofFullyFaithful G⟩⟩

/-- In an adjoint triple `L ⊣ M ⊣ R`, the left adjoint `L` is full and faithful if and only if
the right adjoint `R` is.  This is the `Prop`-valued form of
`CategoryTheory.Adjunction.Triple.fullyFaithfulEquiv`. -/
@[sga "4 I 5.7" "Remark 5.7 a)", sga "4 III 2.6" "more general"]
private lemma full_and_faithful_iff_of_triple {C : Type*} [Category C] {D : Type*} [Category D]
    {L R : C ⥤ D} {M : D ⥤ C} (t : Adjunction.Triple L M R) :
    (L.Full ∧ L.Faithful) ↔ (R.Full ∧ R.Faithful) := by
  rw [← nonempty_fullyFaithful_iff_full_and_faithful,
    ← nonempty_fullyFaithful_iff_full_and_faithful]
  exact t.fullyFaithfulEquiv.nonempty_congr

/-- **Stacks 04GZ (2).** The adjoint triple `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}` carried by the
localization morphism `j_F : E/F ⟶ E`: its lower shriek is `Over.forget F`, by
`MorphismOfTopoi.overLocalizationShriek`, and its pushforward is the given right adjoint `p` of
`j_F⁻¹ = toOver F`. -/
private def overLocalizationTriple {E : Type u} [Category.{v} E] [CartesianMonoidalCategory E]
    (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) :
    Adjunction.Triple (Over.forget F) (toOver F) p where
  adj₁ := MorphismOfTopoi.overLocalizationShriek F adj
  adj₂ := adj
end

end Stacks.Subtopos.SubterminalCriterion

@[expose] public section

open Stacks.Subtopos.SubterminalCriterion in
/-- **Stacks 08LW.** Let `E` be a topos and `F` an object of `E` (in the source, a sheaf on a
site `C`), and let `j_F : E/F ⟶ E` be the localization morphism of Stacks 04GZ, given by a right
adjoint `p` of `j_F⁻¹ = toOver F`. Then `j_F` is an embedding of topoi — so that `E/F` is the
subtopos `j_{F,*}(E/F)` of `E` — if and only if `F` is a subobject of the final object of `E`. -/
@[stacks 08LW "The localization j_F : E/F ⟶ E is an embedding of topoi, i.e. E/F is a subtopos of
E, if and only if F is a subobject of the final object.",
  sga "4 IV 9.2.1" "(9.2.2) is an embedding", sga "4 VI 4.1" "open inclusion j"]
public theorem MorphismOfTopoi.isEmbedding_overLocalization_iff_isSubterminal {E : Type u}
    [Category.{v} E] [CartesianMonoidalCategory E] (F : E) {p : Over F ⥤ E}
    (adj : toOver F ⊣ p) :
    (MorphismOfTopoi.overLocalization F adj).IsEmbedding ↔ IsSubterminal F :=
  calc (MorphismOfTopoi.overLocalization F adj).IsEmbedding
      ↔ (Over.forget F).Full ∧ (Over.forget F).Faithful :=
        (full_and_faithful_iff_of_triple (overLocalizationTriple F adj)).symm
    _ ↔ (Over.forget F).Full := and_iff_left inferInstance
    _ ↔ IsSubterminal F := full_overForget_iff_isSubterminal F
end

end

end CategoryTheory.Sites.Subtopos

/-!
# The closed complement of a sheaf is a subtopos

Let `(C, J)` be a site and let `F` be a sheaf on it. The *closed complement* of `F` is the
strictly full subcategory `closedComplement F` of `Sh(C, J)` consisting of those sheaves `G`
for which the projection `F ⨯ G ⟶ F` is an isomorphism; since limits of sheaves of sets are
computed on sections, `G` lies in it precisely when `G(V)` is a singleton for every object `V`
with `F(V) ≠ ∅`. For `F` a subsheaf of the final object `*`, so that `Sh(C, J)/F` is the open
subtopos of `F` (Stacks 08LW, 08LX), this is the complementary closed part: for `C` the site of
opens of a topological space `X` and `F = h_U` the sheaf of an open `U`, it is the subcategory
of sheaves that are singletons on every open contained in `U`, that is, the sheaves supported on
the closed set `X \ U`.

Stacks 08LY says that the closed complement is a subtopos of `Sh(C, J)` in the sense of
Stacks 08LV: it is the essential image of the pushforward of an embedding of topoi. The
embedding can be taken to have the *same* underlying category `C`, carrying the finer topology
in which a sieve `S` on `V` covers as soon as `S` together with the sieve
`{W ⟶ V | F(W) ≠ ∅}` covers for `J`; its pushforward is the inclusion of the finer sheaves
into `Sh(C, J)`, which is fully faithful, and a sheaf for the finer topology is exactly one
that is a singleton wherever `F` has a section, the empty sieve covering every such object.
This is what makes the definition of a closed subtopos (Stacks 08LZ) legitimate.

## Main results

* `isSubtopos_closedComplement` (Stacks 08LY): the closed complement of a sheaf `F` on a site
  `(C, J)` is a subtopos of `Sh(C, J)`.

## Implementation notes

Departures from the form of the source, none of them weakenings.

* No hypothesis that `F` be a subsheaf of the final object. The source's own proof never uses
  it, and the statement is true for every sheaf: only the image of `F ⟶ *` matters, since
  `closedComplement F` depends on `F` merely through the objects `V` with `F(V) ≠ ∅`. Concretely,
  the source reduces (by Stacks 03CI, which representably realizes *any* sheaf) to `F = h_U` with
  `X` final in `C`, and then argues that `G` lies in the subcategory if and only if
  `G(U ×_X V)` is a singleton for all `V`; that equivalence needs no monomorphism, because
  `U ×_X V ⟶ V` admits the section `(a, 1)` for every `a : V ⟶ U`, so `G(V)` is a retract of
  `G(U ×_X V)` in `Type`. Dropping the hypothesis is what makes the closed complement of an
  arbitrary sheaf usable, and it gives `IsClosedSubtopos J P → IsSubtopos J P` at once.
* Sheaves of sets are taken in `Type (max u v)`, the canonical size for a site `C : Type u` with
  `Category.{v} C`, as in the treatment of closed immersions in this library. It is the size at
  which every Grothendieck topology on `C` admits sheafification
  (`CategoryTheory.instHasSheafifyType`), hence at which `Sh(C, J)` is a topos and the inclusion
  of a finer category of sheaves has the exact left adjoint that an embedding of topoi requires.
* "Is a subtopos" is Stacks 08LV as formalized by `IsSubtopos`, an equality of the essential
  image of an embedding's pushforward with the given `ObjectProperty`; no equivalence of
  categories is substituted for it. Its witnessing site is quantified in the universes of `C`,
  which the topology described above provides.

Faithfulness.

1. Every hypothesis is used by the conclusion: the site `(C, J)` and the sheaf `F` are all there
   is, and the conclusion is about the subcategory `F` cuts out. The source's monomorphism
   hypothesis is absent rather than unused, as explained above.
2. The base is the source's: `C` with the source's topology `J`, sheaves of sets on it, and the
   product `F ⨯ G` and the subcategory both taken in `Sh(C, J)` — not in presheaves, not in a
   localized topos.
3. The map the source names is pinned: `closedComplement F` requires the *projection*
   `prod.fst : F ⨯ G ⟶ F` to be an isomorphism, not the existence of some isomorphism
   `F ⨯ G ≅ F`.
4. Not degenerate. For `F = *` the subcategory is that of the terminal sheaves, the essential
   image of the inclusion of `Sh(C, ⊤)`; for `F` the initial sheaf it is all of `Sh(C, J)`, the
   essential image of the identity; and for `C` the opens of a space and `F = h_U` it is the
   proper, nontrivial subcategory of sheaves supported on the closed complement of `U`.

## References

Stacks Project, Lemma 7.43.5 (tag 08LY, `sites-lemma-closed-subtopos`); Stacks 08LZ defines a
*closed subtopos* to be one of the subtopoi produced here, and Stacks 08M1 lists the exactness
properties of its inclusion.
-/

namespace CategoryTheory.Sites.Subtopos

section

universe v u w v' u'
open CategoryTheory
open CategoryTheory Limits Opposite

namespace Stacks.Subtopos.ClosedComplement

@[expose] public section

/-! ### Projections onto a factor of a binary product -/

section Abstract

/-- A type with a point in which any two elements agree has a unique element. -/
private lemma nonempty_unique_of_forall_eq {α : Sort*} (a : α) (h : ∀ x y : α, x = y) :
    Nonempty (Unique α) :=
  ⟨⟨⟨a⟩, fun _ => h _ _⟩⟩

/-- Any two elements of a type that is known to have a unique element agree. -/
private lemma eq_of_nonempty_unique {α : Sort*} (h : Nonempty (Unique α)) (a b : α) : a = b :=
  h.elim fun _ => Subsingleton.elim a b

variable {D : Type u'} [Category.{v'} D] [HasBinaryProducts D]

/-- In a category with binary products the projection `A ⨯ B ⟶ A` is an isomorphism if and only
if there is exactly one morphism `T ⟶ B` for every object `T` admitting a morphism to `A`. -/
private lemma isIso_prod_fst_iff (A B : D) :
    IsIso (prod.fst : A ⨯ B ⟶ A) ↔ ∀ T : D, (T ⟶ A) → Nonempty (Unique (T ⟶ B)) := by
  constructor
  · intro h T f
    -- both components of a lift of `f` are determined, `prod.fst` being a monomorphism
    have hsub : ∀ a b : T ⟶ B, a = b := fun a b => by
      have h1 : prod.lift f a = prod.lift f b :=
        (cancel_mono (prod.fst : A ⨯ B ⟶ A)).1 (by simp)
      simpa using congrArg (fun k : T ⟶ A ⨯ B => k ≫ (prod.snd : A ⨯ B ⟶ B)) h1
    exact nonempty_unique_of_forall_eq (f ≫ inv (prod.fst : A ⨯ B ⟶ A) ≫ prod.snd) hsub
  · intro h
    let : Unique (A ⟶ B) := (h A (𝟙 A)).some
    let : Unique (A ⨯ B ⟶ B) := (h (A ⨯ B) prod.fst).some
    exact ⟨⟨prod.lift (𝟙 A) default, prod.hom_ext (by simp) (Subsingleton.elim _ _), by simp⟩⟩

end Abstract

section Site

variable {C : Type u} [Category.{v} C]

/-! ### The support sieve of a presheaf -/

/-- The *support sieve* of a presheaf `P` of types at an object `V`: the sieve of those
`f : W ⟶ V` whose source carries a section of `P`. Membership does not depend on `f`, and this is
a sieve because `P` is contravariant. -/
private def supportSieve (P : Cᵒᵖ ⥤ Type w) (V : C) : Sieve V where
  arrows W _ := Nonempty (P.obj (op W))
  downward_closed := fun hf g => hf.elim fun s => ⟨P.map g.op s⟩

private lemma supportSieve_arrows {P : Cᵒᵖ ⥤ Type w} {V W : C} {g : W ⟶ V} :
    (supportSieve P V).arrows g ↔ Nonempty (P.obj (op W)) := Iff.rfl

private lemma supportSieve_eq_top {P : Cᵒᵖ ⥤ Type w} {V : C} (h : Nonempty (P.obj (op V))) :
    supportSieve P V = ⊤ :=
  Sieve.id_mem_iff_eq_top.1 (supportSieve_arrows.2 h)

private lemma pullback_sup_supportSieve {P : Cᵒᵖ ⥤ Type w} {V W : C} (S : Sieve V) (g : W ⟶ V) :
    (S ⊔ supportSieve P V).pullback g = S.pullback g ⊔ supportSieve P W :=
  Sieve.ext fun _ _ => Iff.rfl

/-! ### Sieves over which a presheaf has no choice -/

/-- The property of a sieve `T` on `V` that the presheaf `P` has exactly one section over the
source of every leg of `T`. -/
private def IsSingletonOnSieve (P : Cᵒᵖ ⥤ Type w) {V : C} (T : Sieve V) : Prop :=
  ∀ ⦃W : C⦄ ⦃f : W ⟶ V⦄, T.arrows f → Nonempty (Unique (P.obj (op W)))

/-- A leg of `S ⊔ T` that misses `S` lies in `T`, and so does anything factoring through it;
hence `P` has exactly one section over the source of such a factorisation. -/
private lemma IsSingletonOnSieve.nonempty_unique_of_not_mem {P : Cᵒᵖ ⥤ Type w} {V : C}
    {T : Sieve V} (hT : IsSingletonOnSieve P T) {S : Sieve V} {W Z : C} {f : W ⟶ V}
    (hf : (S ⊔ T : Sieve V).arrows f) (hs : ¬ S.arrows f) (g : Z ⟶ W) :
    Nonempty (Unique (P.obj (op Z))) :=
  hT (T.downward_closed (((Sieve.union_apply f).1 hf).resolve_left hs) g)

/-- Consequently any two sections of `P` over that source agree; this is what makes the extension
of a matching family over the legs outside `S` both possible and unique. -/
private lemma IsSingletonOnSieve.eq_of_not_mem {P : Cᵒᵖ ⥤ Type w} {V : C} {T : Sieve V}
    (hT : IsSingletonOnSieve P T) {S : Sieve V} {W Z : C} {f : W ⟶ V}
    (hf : (S ⊔ T : Sieve V).arrows f) (hs : ¬ S.arrows f) (g : Z ⟶ W)
    (a b : P.obj (op Z)) : a = b :=
  eq_of_nonempty_unique (hT.nonempty_unique_of_not_mem hf hs g) a b

/-- Extension of a matching family for `S` to one for `S ⊔ T`: over a leg outside `S` the value
is forced, `P` having exactly one section there. -/
private noncomputable def extendFamily {P : Cᵒᵖ ⥤ Type w} {V : C} {S T : Sieve V}
    (hT : IsSingletonOnSieve P T) (x : Presieve.FamilyOfElements P S.arrows) :
    Presieve.FamilyOfElements P (S ⊔ T : Sieve V).arrows := fun W f hf =>
  @dite _ (S.arrows f) (Classical.dec _) (fun hs => x f hs)
    (fun hs => (hT.nonempty_unique_of_not_mem hf hs (𝟙 W)).some.default)

private lemma extendFamily_of_mem {P : Cᵒᵖ ⥤ Type w} {V : C} {S T : Sieve V}
    (hT : IsSingletonOnSieve P T) (x : Presieve.FamilyOfElements P S.arrows) {W : C} {f : W ⟶ V}
    (hf : S.arrows f) (hf' : (S ⊔ T : Sieve V).arrows f) :
    extendFamily hT x f hf' = x f hf := by
  simp [extendFamily, hf]

/-- A presheaf of types that is a sheaf for `S ⊔ T` is a sheaf for `S`, provided it has exactly
one section over the source of every leg of `T`: a matching family for `S` has one and only one
extension to `S ⊔ T`, there being nothing to choose over the extra legs. -/
private lemma isSheafFor_of_sup {P : Cᵒᵖ ⥤ Type w} {V : C} {S T : Sieve V}
    (hT : IsSingletonOnSieve P T) (h : Presieve.IsSheafFor P (S ⊔ T : Sieve V).arrows) :
    Presieve.IsSheafFor P S.arrows := by
  intro x hx
  have hy : (extendFamily hT x).Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    by_cases hs₁ : S.arrows f₁
    · by_cases hs₂ : S.arrows f₂
      · rw [extendFamily_of_mem hT x hs₁ h₁, extendFamily_of_mem hT x hs₂ h₂]
        exact hx g₁ g₂ hs₁ hs₂ hcomm
      · exact hT.eq_of_not_mem h₂ hs₂ g₂ _ _
    · exact hT.eq_of_not_mem h₁ hs₁ g₁ _ _
  obtain ⟨t, ht, htuniq⟩ := h _ hy
  refine ⟨t, fun W f hf => ?_, fun t' ht' => htuniq t' fun W f hf => ?_⟩
  · rw [ht f ((Sieve.union_apply f).2 (Or.inl hf))]
    exact extendFamily_of_mem hT x hf _
  · by_cases hs : S.arrows f
    · rw [extendFamily_of_mem hT x hs hf]
      exact ht' f hs
    · exact hT.eq_of_not_mem hf hs (𝟙 W) _ _

/-- The property of a pair of presheaves `P`, `Q` of types that `Q` has exactly one section over
every object over which `P` has a section. -/
private def IsSingletonOnSupport (P Q : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ V : Cᵒᵖ, Nonempty (P.obj V) → Nonempty (Unique (Q.obj V))

/-- A support sieve of `P` is a sieve over which a presheaf that is a singleton on the support of
`P` has no choice: membership in it depends only on the source, where `P` has a section. -/
private lemma IsSingletonOnSupport.isSingletonOnSieve {P Q : Cᵒᵖ ⥤ Type w}
    (h : IsSingletonOnSupport P Q) (V : C) : IsSingletonOnSieve Q (supportSieve P V) := by
  intro W f hf
  exact h _ (supportSieve_arrows.1 hf)

/-- There is exactly one morphism `P ⟶ Q` when `Q` is a singleton on the support of `P`: every
component has a single possible value, so naturality is automatic and no two morphisms differ. -/
private lemma IsSingletonOnSupport.nonempty_unique_hom {P Q : Cᵒᵖ ⥤ Type w}
    (h : IsSingletonOnSupport P Q) : Nonempty (Unique (P ⟶ Q)) := by
  have heq : ∀ V : Cᵒᵖ, P.obj V → ∀ a b : Q.obj V, a = b :=
    fun V z => eq_of_nonempty_unique (h V ⟨z⟩)
  refine nonempty_unique_of_forall_eq
    { app := fun V => ↾fun z => (h V ⟨z⟩).some.default
      naturality := fun V W g => ?_ } fun a b =>
    NatTrans.ext (funext fun V => TypeCat.homEquiv.injective (funext fun z => heq V z _ _))
  exact TypeCat.homEquiv.injective (funext fun z => heq W (P.map g z) _ _)

/-! ### The finer topology -/

/-- The topology on `C` in which a sieve `S` on `V` covers as soon as `S` together with the
support sieve of `P` at `V` covers for `J`. It is finer than `J`, and its sheaves are exactly
the `J`-sheaves that are singletons wherever `P` has a section. -/
private def supportTopology (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) :
    GrothendieckTopology C where
  sieves V := {S | S ⊔ supportSieve P V ∈ J V}
  top_mem' V := by
    simp only [Set.mem_ofPred_eq, top_sup_eq]
    exact J.top_mem V
  pullback_stable' {V W S} g hS := by
    rw [Set.mem_ofPred_eq, ← pullback_sup_supportSieve S g]
    exact J.pullback_stable g (show S ⊔ supportSieve P V ∈ J V from hS)
  transitive' {V S} hS R hR := by
    rw [Set.mem_ofPred_eq]
    refine J.transitive (show S ⊔ supportSieve P V ∈ J V from hS) _ ?_
    intro W g hg
    rw [pullback_sup_supportSieve]
    rcases (Sieve.union_apply g).1 hg with hg | hg
    · exact hR hg
    · refine J.covering_of_eq_top ?_
      rw [supportSieve_eq_top (supportSieve_arrows.1 hg), sup_top_eq]

private lemma mem_supportTopology (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) {V : C}
    {S : Sieve V} : S ∈ supportTopology J P V ↔ S ⊔ supportSieve P V ∈ J V :=
  Iff.rfl

/-- The topology `supportTopology J P` is finer than `J`. -/
private lemma le_supportTopology (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) :
    J ≤ supportTopology J P :=
  fun _ _ hS => J.superset_covering le_sup_left hS

/-- Consequently every sheaf for `supportTopology J P` is a `J`-sheaf. -/
private lemma isSheaf_le (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf (supportTopology J P) (A := Type (max u v)) ≤
      Presheaf.IsSheaf J (A := Type (max u v)) :=
  fun _ h => h.of_le (le_supportTopology J P)

/-! ### Sheaves for the finer topology -/

variable {J : GrothendieckTopology C}

/-- A `J`-sheaf is a sheaf for the finer topology exactly when it has one section over every
object over which `F` has a section. -/
private lemma isSheaf_supportTopology_iff {F G : Sheaf J (Type (max u v))} :
    Presheaf.IsSheaf (supportTopology J F.obj) G.obj ↔ IsSingletonOnSupport F.obj G.obj := by
  constructor
  · intro hG V hV
    obtain ⟨V⟩ := V
    have hbot : (⊥ : Sieve V) ∈ supportTopology J F.obj V := by
      rw [mem_supportTopology, bot_sup_eq, supportSieve_eq_top hV]
      exact J.top_mem V
    exact ⟨Limits.Types.isTerminalEquivUnique _
      (Sheaf.isTerminalOfBotCover (⟨G.obj, hG⟩ : Sheaf (supportTopology J F.obj) _) V hbot)⟩
  · intro hG
    rw [isSheaf_iff_isSheaf_of_type]
    intro V S hS
    exact isSheafFor_of_sup (hG.isSingletonOnSieve V)
      (G.property.isSheafFor _ (show S ⊔ supportSieve F.obj V ∈ J V from hS))

/-! ### The closed complement in terms of sections -/

/-- Testing on the sheafifications of the representable presheaves: `G` has exactly one section
over every object over which `F` has a section if and only if there is exactly one morphism
`T ⟶ G` for every sheaf `T` admitting a morphism to `F`. -/
private lemma isSingletonOnSupport_iff {F G : Sheaf J (Type (max u v))} :
    (∀ T : Sheaf J (Type (max u v)), (T ⟶ F) → Nonempty (Unique (T ⟶ G))) ↔
      IsSingletonOnSupport F.obj G.obj := by
  constructor
  · intro h V hV
    have e : ∀ H : Sheaf J (Type (max u v)),
        ((presheafToSheaf J (Type (max u v))).obj (uliftYoneda.{u}.obj V.unop) ⟶ H) ≃
          H.obj.obj V := fun H =>
      ((sheafificationAdjunction J (Type (max u v))).homEquiv _ H).trans
        (uliftYonedaEquiv.{u} (X := V.unop))
    obtain ⟨u⟩ := h _ ((e F).symm hV.some)
    let := u
    exact ⟨(e G).symm.unique⟩
  · intro hG T t
    -- `t` carries the sections of `T` into `F`, so `G` is a singleton on the support of `T` too
    have h : IsSingletonOnSupport T.obj G.obj := fun V hz =>
      hG V (hz.elim fun z => ⟨t.hom.app V z⟩)
    obtain ⟨u⟩ := h.nonempty_unique_hom
    exact nonempty_unique_of_forall_eq (ObjectProperty.homMk u.default) fun a b =>
      Sheaf.hom_ext ((u.uniq a.hom).trans (u.uniq b.hom).symm)

/-- The sheaves in the closed complement of `F` are exactly those with one section over every
object over which `F` has a section. -/
private lemma closedComplement_iff (F G : Sheaf J (Type (max u v))) :
    closedComplement F G ↔ IsSingletonOnSupport F.obj G.obj :=
  (isIso_prod_fst_iff F G).trans isSingletonOnSupport_iff

/-! ### The embedding of topoi -/

/-- The inclusion of the sheaves for the finer topology into `Sh(C, J)`. -/
private def incl (F : Sheaf J (Type (max u v))) :
    Sheaf (supportTopology J F.obj) (Type (max u v)) ⥤ Sheaf J (Type (max u v)) :=
  ObjectProperty.ιOfLE (isSheaf_le J F.obj)

/-- The morphism of topoi `Sh(C, J_F) ⟶ Sh(C, J)` whose pushforward is the inclusion and whose
inverse image is sheafification for the finer topology. -/
@[sga "4 IV 9.3.5"]
private noncomputable def morphism (F : Sheaf J (Type (max u v))) :
    MorphismOfTopoi (Sheaf (supportTopology J F.obj) (Type (max u v)))
      (Sheaf J (Type (max u v))) where
  pushforward := incl F
  inverseImage := sheafToPresheaf J (Type (max u v)) ⋙
    presheafToSheaf (supportTopology J F.obj) (Type (max u v))
  adj := Adjunction.restrictFullyFaithful
    (sheafificationAdjunction (supportTopology J F.obj) (Type (max u v)))
    (fullyFaithfulSheafToPresheaf J (Type (max u v))) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)
  preservesFiniteLimits := by
    have : PreservesLimits (sheafToPresheaf J (Type (max u v))) :=
      (sheafificationAdjunction J (Type (max u v))).rightAdjoint_preservesLimits
    exact comp_preservesFiniteLimits _ _

/-- The morphism of topoi is an embedding: its pushforward is the inclusion of a full
subcategory. -/
private lemma isEmbedding (F : Sheaf J (Type (max u v))) : (morphism F).IsEmbedding :=
  ⟨ObjectProperty.full_ιOfLE (isSheaf_le J F.obj),
    ObjectProperty.faithful_ιOfLE (isSheaf_le J F.obj)⟩

/-- The essential image of the inclusion is the closed complement of `F`: a `J`-sheaf is in the
image exactly when its underlying presheaf is a sheaf for the finer topology. -/
private lemma essImage_incl (F : Sheaf J (Type (max u v))) :
    (incl F).essImage = closedComplement F := by
  funext G
  refine propext ⟨?_, ?_⟩
  · rintro ⟨H, ⟨e⟩⟩
    refine (closedComplement_iff F G).2 (isSheaf_supportTopology_iff.1 ?_)
    exact (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf J (Type (max u v))).mapIso e)).1 H.property
  · intro hG
    exact ⟨⟨G.obj, isSheaf_supportTopology_iff.2 ((closedComplement_iff F G).1 hG)⟩,
      ⟨ObjectProperty.isoMk _ (Iso.refl G.obj)⟩⟩

end Site
end

end Stacks.Subtopos.ClosedComplement

@[expose] public section

open Stacks.Subtopos.ClosedComplement in
/-- **Stacks Project, Lemma 7.43.5 (tag 08LY).** Let `(C, J)` be a site and let `F` be a sheaf
of sets on it. The strictly full subcategory `closedComplement F` of `Sh(C, J)`, consisting of
the sheaves `G` for which the projection `F ⨯ G ⟶ F` is an isomorphism, is a subtopos of
`Sh(C, J)`: it is the essential image of the pushforward of an embedding of topoi.

The source assumes `F` to be a subsheaf of the final object, in which case this closed subtopos
is complementary to the open subtopos `Sh(C, J)/F` of Stacks 08LW; the hypothesis is not needed,
as `closedComplement F` depends on `F` only through the objects on which `F` has a section. -/
@[stacks 08LY "The full subcategory of sheaves G with F ⨯ G ⟶ F an isomorphism is a subtopos of
Sh(C). Stated for an arbitrary sheaf F, the source's hypothesis that F be a subsheaf of the
final object being unused in its proof.",
  sga "4 IV 9.3.1" "for any topos and open U",
  sga "4 IV 9.3.4" "partial",
  sga "4 VI 4.1" "partial"]
public theorem isSubtopos_closedComplement {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (F : Sheaf J (Type (max u v))) :
    IsSubtopos J (closedComplement F) :=
  ⟨C, inferInstance, supportTopology J F.obj, morphism F, isEmbedding F, essImage_incl F⟩
end

end

end CategoryTheory.Sites.Subtopos

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Subterminal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Open subtopoi

A strictly full subcategory `E ⊆ Sh(C)` closed under isomorphisms is an *open subtopos* when
there is a subsheaf `F` of the terminal sheaf together with an equivalence `E ≌ Sh(C)/F`
compatible with the two functors into `Sh(C)` (Stacks 08LX).  What justifies modelling
"`Sh(C)/F` is a subtopos of `Sh(C)`" by full faithfulness of `Over.forget F` is Stacks lemma
08LW, proved here: for an object `X` of any category, `Over.forget X` is full — faithful it
always is — if and only if `X` is a subobject of the final object, that is, any two morphisms
into `X` agree.  When a terminal object is available this says that `X ⟶ ⊤` is a monomorphism.

## Main definitions

* `OpenSubtopos.IsSubobjectOfTerminal`: the unique morphism from a sheaf to the terminal sheaf
  is a monomorphism.
* `OpenSubtopos.IsSubtoposOver`: `Over.forget F` is fully faithful, which is how "`Sh(C)/F` is a
  subtopos of `Sh(C)`" is modelled.
* `OpenSubtopos.IsOpenSubtopos`: a strictly full subcategory of `Sh(C)` is an *open subtopos*
  when it is `Sh(C)/F` for a subsheaf `F` of the terminal sheaf (Stacks 08LX).

## Main results

* `full_overForget_iff_isSubterminal`: `Over.forget X` is full if and only if `X` is a subobject
  of the final object (Stacks 08LW).
* `over_forget_fullyFaithful_iff_mono_terminalFrom`: the same in a category with a terminal
  object, in the `Mono (Limits.terminal.from X)` spelling.
* `isSubobjectOfTerminal_iff_isSubtoposOver`: a sheaf `F` is a subobject of the terminal sheaf if
  and only if `Sh(C)/F` is a subtopos of `Sh(C)`.

## Implementation notes

`full_overForget_iff_isSubterminal` asks for no terminal object and has no `Faithful` conjunct:
`Over.forget X` is faithful for every `X`, so a conjunct asking for it would make the equivalence
unusable as a rewrite, and "any two morphisms into `X` agree" is `CategoryTheory.IsSubterminal X`,
which mentions no chosen terminal object.  That is the form both directions of the proof produce.
The terminal-object spelling is the corollary `over_forget_fullyFaithful_iff_mono_terminalFrom`,
kept because the definitions here say "subsheaf of the terminal sheaf" as
`Mono (Limits.terminal.from F)`.

Tags covered: 08LX.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace OpenSubtopos

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/--
`IsSubobjectOfTerminal F` says that the unique map from `F` to the terminal
object of `Sh(C)` is a monomorphism. This is the precise formalization of
"`F` is a subobject of the final object of `Sh(C)`".
-/
@[sga "4 IV 8.3",
  sga "4 IV 9.2.1" "special case",
  sga "4 V 4.16",
  sga "4 VI 4.1",
  sga "4½ Cycle 1.1.4"]
def IsSubobjectOfTerminal [Limits.HasTerminal (Sheaf J (Type w))]
    (F : Sheaf J (Type w)) : Prop :=
  Mono (Limits.terminal.from F)

/--
`IsSubtoposOver F` says that the topos `Sh(C)/F` is a subtopos of `Sh(C)`.
We model "subtopos" via the canonical functor
`Over.forget F : Over F ⥤ Sheaf J (Type w)` — which realizes the `j_!`
functor of the localization morphism of topoi `j_F : Sh(C)/F → Sh(C)` — being
fully faithful. This is the standard categorical characterization of an
inclusion (geometric embedding) of topoi at the level of `j_!`.
-/
@[sga "4 IV 5.7"]
def IsSubtoposOver (F : Sheaf J (Type w)) : Prop :=
  (Over.forget F).Full ∧ (Over.forget F).Faithful

/--
**Open subtopos.**

A strictly full subcategory `E ⊂ Sh(C)`, modelled as an
`ObjectProperty (Sheaf J (Type w))` closed under isomorphisms, is an
*open subtopos* of `Sh(C)` if there exists a subsheaf `F` of the terminal
sheaf such that `E` is the subtopos `Sh(C)/F`. We capture "`E` is the
subtopos `Sh(C)/F`" by an equivalence of categories
`P.FullSubcategory ≌ Over F` compatible with the inclusion `P.ι` into
`Sh(C)` and the canonical forgetful functor `Over.forget F`.
-/
@[stacks 08LX]
def IsOpenSubtopos [Limits.HasTerminal (Sheaf J (Type w))]
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
  ∃ (F : Sheaf J (Type w)) (_ : Mono (Limits.terminal.from F))
    (e : P.FullSubcategory ≌ Over F),
    Nonempty (e.functor ⋙ Over.forget F ≅ P.ι)

end OpenSubtopos

/-! ## Fullness of `Over.forget` (Stacks 08LW) -/

/--
If `Over.forget X : Over X ⥤ D` is full, then any two morphisms `f g : Y ⟶ X`
agree: by fullness the identity of `Y` lifts to a morphism
`Over.mk f ⟶ Over.mk g`, whose commutativity condition is `f = g`.
-/
lemma full_overForget_imp_hom_eq
    {D : Type u} [Category.{v} D] (X : D)
    [(Over.forget X).Full] {Y : D} (f g : Y ⟶ X) : f = g := by
  obtain ⟨φ, hφ⟩ := (Over.forget X).map_surjective
    (X := Over.mk f) (Y := Over.mk g) (𝟙 Y)
  simpa [Over.mk, show φ.left = 𝟙 Y from hφ] using (Over.w φ).symm

/--
For an object `X` of any category, `Over.forget X : Over X ⥤ D` is full if and
only if `X` is a subobject of the final object, that is, any two morphisms into
`X` agree; faithful `Over.forget X` always is. This is the categorical content
of Stacks Lemma 08LW, and needs no terminal object to be stated.
-/
@[sga "4 IV 9.2.1" "partial"]
theorem full_overForget_iff_isSubterminal {D : Type u} [Category.{v} D] (X : D) :
    (Over.forget X).Full ↔ IsSubterminal X :=
  ⟨fun _ _ => full_overForget_imp_hom_eq X,
    fun h => ⟨fun f => ⟨Over.homMk f (h _ _), rfl⟩⟩⟩

/-! ## The same in the `Mono (Limits.terminal.from X)` spelling -/

/--
If any two morphisms into `X` agree, then the unique morphism
`Limits.terminal.from X` is a monomorphism. The hypothesis is
`CategoryTheory.IsSubterminal X` with its object binder unbundled, and the
proof is that fact's `CategoryTheory.IsSubterminal.mono_terminal_from`.
-/
lemma mono_terminalFrom_of_hom_eq
    {D : Type u} [Category.{v} D] [Limits.HasTerminal D] (X : D)
    (h : ∀ {Y : D} (f g : Y ⟶ X), f = g) :
    Mono (Limits.terminal.from X) :=
  IsSubterminal.mono_terminal_from fun _ f g => h f g

/--
If `Limits.terminal.from X` is a monomorphism, then `Over.forget X` is full:
any two morphisms into `X` agree, being equal after the monomorphism
`X ⟶ ⊤_ D`, so `full_overForget_iff_isSubterminal` applies.
-/
lemma full_overForget_of_mono_terminalFrom
    {D : Type u} [Category.{v} D] [Limits.HasTerminal D] (X : D)
    (h : Mono (Limits.terminal.from X)) :
    (Over.forget X).Full :=
  (full_overForget_iff_isSubterminal X).2 (@isSubterminal_of_mono_terminal_from _ _ X _ h)

/--
For an object `X` in a category `D` with a terminal object, the forgetful
functor `Over.forget X : Over X ⥤ D` is fully faithful (both `Full` and
`Faithful`) if and only if the unique morphism `X ⟶ ⊤_ D` is a monomorphism.
This is `full_overForget_iff_isSubterminal` in the spelling the definitions
above use: the `Faithful` conjunct is free, and subterminality of `X` is
monicity of `X ⟶ ⊤_ D`.
-/
theorem over_forget_fullyFaithful_iff_mono_terminalFrom
    {D : Type u} [Category.{v} D] [Limits.HasTerminal D] (X : D) :
    ((Over.forget X).Full ∧ (Over.forget X).Faithful) ↔
      Mono (Limits.terminal.from X) :=
  ⟨fun h => ((full_overForget_iff_isSubterminal X).1 h.1).mono_terminal_from,
    fun h => ⟨full_overForget_of_mono_terminalFrom X h, inferInstance⟩⟩

/--
Specialization to sheaves: `F` is a subobject of the terminal sheaf if and
only if `Sh(C)/F` is a subtopos of `Sh(C)`, in the sense that `Over.forget F`
is fully faithful.
-/
theorem isSubobjectOfTerminal_iff_isSubtoposOver
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [Limits.HasTerminal (Sheaf J (Type w))] (F : Sheaf J (Type w)) :
    OpenSubtopos.IsSubobjectOfTerminal J F ↔
      OpenSubtopos.IsSubtoposOver J F :=
  (over_forget_fullyFaithful_iff_mono_terminalFrom F).symm

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.TrivialComposite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor

/-!
# Lifting trivial objects along an exact functor of Galois categories

Let `H : C ⥤ D` and `H' : D ⥤ E` be functors, with `D` and `E` Galois categories whose fibre
functors are identified by a natural isomorphism `H' ⋙ F' ≅ F`. Suppose that every connected
object of `D` whose image under `H'` admits a morphism from a terminal object lies in the
essential image of `H`. Then every object of `D` whose image under `H'` is a finite coproduct of
terminal objects lies in the essential image of `H`.

The proof rests on the fibre functor of a Galois category being faithful, so that a monomorphism
is detected on fibres, together with the following observation: if a monomorphism `A ⟶ V` has
nonempty source fibre and `V` is a finite coproduct of terminal objects, then some terminal
object maps to `A`: a point of the fibre of `A` lands in one of the summands of `V`, and the
pullback of that summand along the monomorphism has a fibre which is both nonempty and
subsingleton, hence is carried to an isomorphism by the fibre functor. Decomposing an object of
`D` into its connected components and applying the hypothesis to each component then exhibits
the object as the image of a finite coproduct in `C`.

## Main results

* `CategoryTheory.terminal_map_of_mono_into_finiteCoproductTerminal` — a subobject with nonempty
  fibre of a finite coproduct of terminal objects receives a morphism from a terminal object.
* `CategoryTheory.essImage_of_trivial_of_connected_lifting` — an object whose image under `H'` is
  a finite coproduct of terminal objects lies in the essential image of `H`, provided the
  connected objects with that property do.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' u'' v'' w

namespace CategoryTheory

/-- Let `i : A ⟶ V` be a monomorphism in a Galois category, with `A` having a nonempty fibre and
`V` a finite coproduct of terminal objects. Then there is a terminal object admitting a morphism
to `A`. -/
theorem terminal_map_of_mono_into_finiteCoproductTerminal {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] {A V : C} (i : A ⟶ V) [Mono i]
    (ha : Nonempty (F.obj A)) (hV : IsFiniteCoproductOfTerminal V) :
    ∃ Z : C, Nonempty (IsTerminal Z) ∧ Nonempty (Z ⟶ A) := by
  obtain ⟨n, B, b, hB, ⟨hb⟩⟩ := hV
  obtain ⟨a⟩ := ha
  obtain ⟨j, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit F B b hb) (F.map i a)
  let P := pullback i (b j)
  let e : F.obj P ≃ {p : F.obj A × F.obj (B j) // F.map i p.1 = F.map (b j) p.2} :=
    (PreservesPullback.iso F i (b j) ≪≫
      Types.pullbackIsoPullback (F.map i) (F.map (b j))).toEquiv
  have hP : Nonempty (F.obj P) := ⟨e.symm ⟨(a, y), hy.symm⟩⟩
  let : Unique (F.obj (B j)) :=
    Types.isTerminalEquivUnique _ ((hB j).some.isTerminalObj F (B j))
  have : IsIso (F.map (pullback.snd i (b j))) := (ConcreteCategory.isIso_iff_bijective _).2
    ⟨(mono_iff_injective _).1 inferInstance, fun _ ↦ ⟨hP.some, Subsingleton.elim _ _⟩⟩
  have : IsIso (pullback.snd i (b j)) := isIso_of_reflects_iso _ F
  exact ⟨B j, hB j, ⟨inv (pullback.snd i (b j)) ≫ pullback.fst i (b j)⟩⟩

/-- Let `H : C ⥤ D` preserve finite colimits and let `H' : D ⥤ E` preserve finite limits, where
`D` and `E` are Galois categories with fibre functors `F` and `F'` identified by a natural
isomorphism `H' ⋙ F' ≅ F`. If every connected object of `D` admitting a morphism from a terminal
object after applying `H'` lies in the essential image of `H`, then so does every object `V`
whose image `H'.obj V` is a finite coproduct of terminal objects. -/
theorem essImage_of_trivial_of_connected_lifting {C : Type u} [Category.{v, u} C]
    {D : Type u'} [Category.{v', u'} D] {E : Type u''} [Category.{v'', u''} E]
    [HasFiniteColimits C] (F : D ⥤ Type w) (F' : E ⥤ Type w)
    [IsGaloisCategory F] [IsGaloisCategory F'] (H : C ⥤ D) (H' : D ⥤ E)
    [PreservesFiniteColimits H] [PreservesFiniteLimits H'] (α : H' ⋙ F' ≅ F)
    (hconn : ∀ A : D, PreGaloisCategory.IsConnected A →
      (∃ Z : E, Nonempty (IsTerminal Z) ∧ Nonempty (Z ⟶ H'.obj A)) → H.essImage A)
    (V : D) (hV : IsFiniteCoproductOfTerminal (H'.obj V)) :
    H.essImage V := by
  classical
  obtain ⟨ι, A, a, ha, hfin, hA⟩ :=
    IsGaloisCategory.exists_finite_coproduct_connected (F := F) V
  have hFA := isColimitCofanMkObjOfIsColimit F A a ha
  have hdesc (j : ι) : H.essImage (A j) := by
    have : Mono (a j) := Functor.mono_of_mono_map F
      ((mono_iff_injective _).2 (Cofan.inj_injective_of_isColimit hFA j))
    have hne : Nonempty (F.obj (A j)) := by
      by_contra hn
      exact (hA j).notInitial
        ((isInitial_iff_isEmpty_fiber F (A j)).2 (not_nonempty_iff.mp hn)).some
    exact hconn (A j) (hA j) (terminal_map_of_mono_into_finiteCoproductTerminal F'
      (H'.map (a j)) ⟨(α.app (A j)).inv hne.some⟩ hV)
  let B : ι → C := fun j ↦ (hdesc j).witness
  let αA : Discrete.functor (fun j ↦ H.obj (B j)) ≅ Discrete.functor A :=
    Discrete.natIso (fun j ↦ (hdesc j.as).getIso)
  have hc : IsColimit ((Cocone.precompose αA.hom).obj (Cofan.mk V a)) :=
    (IsColimit.precomposeHomEquiv αA _).symm ha
  have hH := isColimitCofanMkObjOfIsColimit H B (fun j ↦ Sigma.ι B j) (coproductIsCoproduct B)
  exact ⟨∐ B, ⟨hH.coconePointUniqueUpToIso hc⟩⟩

end CategoryTheory

end

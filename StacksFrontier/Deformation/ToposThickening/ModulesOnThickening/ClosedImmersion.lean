module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Criterion
public import StacksFrontier.CategoryTheory.Sites.ClosedImmersion.Basic
public import StacksFrontier.CategoryTheory.Sites.EmptySheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Subtopos.ClosedImmersion
public import StacksFrontier.Deformation.ToposThickening.Basic

/-!
# A first order thickening as a closed immersion of ringed topoi

A first order thickening `i : (Sh(C), O') ⟶ (Sh(D), O)` of ringed topoi is in particular a
closed immersion of ringed topoi in the sense of Stacks 18.25: its underlying morphism of topoi
is an equivalence, so its direct image is fully faithful and essentially surjective, and a
subtopos which is the whole of `Sh(D)` is the closed complement of the sheaf supported on the
objects covered by the empty sieve.

What that buys is that the essential-image and full-faithfulness results for the direct image on
modules along a closed immersion
(`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates` and
`.pushforwardModules_fullyFaithful`) apply to a thickening.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickening.closedRingedImmersion`: a thickening read as
  a closed immersion of ringed topoi.
* `Deformation.ToposThickening.FirstOrderThickening.structureMap_surjective`: its structure map
  is locally surjective on underlying sheaves of sets.

## Main results

* `Deformation.ToposThickening.mono_terminal_from_emptySheaf` and
  `Deformation.ToposThickening.isIso_prod_fst_emptySheaf`: `CategoryTheory.emptySheaf`, the
  sheaf of sets with a section over exactly the objects covered by the empty sieve, is a
  subsheaf of the terminal object whose closed complement is everything.  An abstract initial
  object would not give these two properties without the strictness of the initial object of a
  topos, which is why the empty sheaf itself is used.

## Implementation notes

The hypotheses are exactly those of `Deformation.ToposThickening.FirstOrderThickening`: the four
`GrothendieckTopology.HasSheafCompose` instances that
`AlgebraicGeometry.RingedToposHom` itself demands, and nothing else. In particular the two ringed
topoi share their section universe, which `AlgebraicGeometry.ClosedRingedImmersion` requires and
`FirstOrderThickening` does not.

## References

* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)

universe v u v' u' w

namespace Deformation.ToposThickening

/-! ### The sheaf supported on the objects covered by the empty sieve -/

section EmptySheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The empty-sieve sheaf is a subsheaf of the terminal sheaf: its sections form a
subsingleton. -/
lemma mono_terminal_from_emptySheaf :
    Mono (terminal.from (emptySheaf.{u, v, w} J)) := by
  apply (sheafToPresheaf J (Type w)).mono_of_mono_map
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro a b _
  cases a
  cases b
  congr 1
  exact Subsingleton.elim _ _

/-- The closed complement of the empty-sieve sheaf is everything: over an object with empty
covering sieve every sheaf has exactly one section, and elsewhere the empty-sieve sheaf has
none, so the projection off it is bijective on sections. -/
lemma isIso_prod_fst_emptySheaf (G : Sheaf J (Type w)) :
    IsIso (Limits.prod.fst : emptySheaf.{u, v, w} J ⨯ G ⟶ emptySheaf J) := by
  let E := emptySheaf.{u, v, w} J
  let F := sheafToPresheaf J (Type w)
  let p : E ⨯ G ⟶ E := Limits.prod.fst
  have hp : ∀ U, IsIso ((F.map p).app U) := by
    intro U
    let A := E.obj.obj U
    let B := G.obj.obj U
    let Cmp := Limits.prodComparison F E G
    have : IsIso Cmp := inferInstance
    let P := F.obj E
    let Q := F.obj G
    let ev := (evaluation Cᵒᵖ (Type w)).obj U
    let cEval := Limits.prodComparison ev P Q
    have : IsIso cEval := inferInstance
    have hfstPair : IsIso (↾_root_.Prod.fst : A × B ⟶ A) := by
      rw [isIso_iff_bijective]
      show Function.Bijective (fun z : A × B => z.1)
      by_cases hU : (⊥ : Sieve U.unop) ∈ J U.unop
      · let : Unique A :=
          { default := ⟨⟨hU⟩⟩
            uniq := by
              intro a
              cases a
              rfl }
        have hB := G.isTerminalOfBotCover U.unop hU
        let : Unique B := Types.isTerminalEquivUnique _ hB
        exact ⟨fun x y h => Prod.ext h (Subsingleton.elim _ _), fun a => ⟨(a, default), rfl⟩⟩
      · let : IsEmpty A := ⟨fun a => hU a.down.down⟩
        exact ⟨fun x _ _ => isEmptyElim x.1, fun a => isEmptyElim a⟩
    have hfst : IsIso (Limits.prod.fst : A ⨯ B ⟶ A) := by
      rw [← Types.binaryProductIso_hom_comp_fst A B]
      infer_instance
    have hEval : cEval ≫ (Limits.prod.fst : A ⨯ B ⟶ A) =
        (Limits.prod.fst : P ⨯ Q ⟶ P).app U :=
      Limits.prodComparison_fst ev P Q
    have hOuter : Cmp.app U ≫ (Limits.prod.fst : P ⨯ Q ⟶ P).app U =
        (F.map p).app U :=
      congrArg (fun f => f.app U) (Limits.prodComparison_fst F E G)
    rw [← hOuter, ← hEval]
    infer_instance
  have : IsIso (F.map p) := NatIso.isIso_of_isIso_app (F.map p)
  exact isIso_of_reflects_iso p F

end EmptySheaf

/-! ### A thickening as a closed immersion -/

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying morphism of topoi of a first order thickening is a closed immersion: it is an
equivalence, hence an embedding whose direct image is essentially surjective, and the whole
topos is the closed complement of the empty-sieve sheaf. -/
lemma FirstOrderThickening.isClosedImmersion {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) :
    MorphismOfTopoi.IsClosedImmersion i.toToposHom := by
  have : i.toToposHom.pushforward.IsEquivalence := hi.equiv
  refine ⟨⟨Functor.IsEquivalence.full, Functor.IsEquivalence.faithful⟩, ?_⟩
  refine ⟨emptySheaf.{u', v', w} Y.J, mono_terminal_from_emptySheaf Y.J, ?_⟩
  ext G
  exact ⟨fun _ => Functor.EssSurj.mem_essImage i.toToposHom.pushforward G,
    fun _ => isIso_prod_fst_emptySheaf Y.J G⟩

/-- The structure map of a first order thickening is locally surjective on the underlying
sheaves of sets. -/
lemma FirstOrderThickening.structureMap_surjective {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) :
    Sheaf.IsLocallySurjective (Y.forgetRing.map i.fSharp) := by
  have : Presheaf.IsLocallySurjective Y.J i.fSharp.hom := hi.surjective
  have h0 : Presheaf.IsLocallySurjective Y.J
      (Functor.whiskerRight i.fSharp.hom (forget CommRingCat.{w})) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective Y.J
      ((sheafToPresheaf Y.J (Type w)).map (Y.forgetRing.map i.fSharp)) := h0
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).1 hsurj

/-- A first order thickening of ringed topoi, read as a closed immersion of ringed topoi. -/
noncomputable def FirstOrderThickening.closedRingedImmersion {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) : ClosedRingedImmersion.{v, u, v', u', w} where
  source := X
  target := Y
  hom := i
  isClosedImmersion := hi.isClosedImmersion
  structureMap_surjective := hi.structureMap_surjective

end Deformation.ToposThickening

end

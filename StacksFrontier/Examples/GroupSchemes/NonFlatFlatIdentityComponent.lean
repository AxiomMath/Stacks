module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Topology.Connected.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsNoLeftAdjoint
public import StacksFrontier.Examples.GroupSchemes.XorGroup

/-!
# A non-flat group scheme whose identity component is flat

Let `i : X ⟶ S` be a monomorphism of schemes, for instance a closed immersion. The disjoint
union `S ⊔ X`, viewed over `S` by the identity on the first summand and by `i` on the second,
carries a group law over `S`: multiplication adds the labels of the two summands modulo two. The
summand labelled `false` is a copy of the base, so it is the identity component, and it is flat
over the base; the whole group scheme is flat over the base only if `i` is.

Taking `i` to be `Spec (ℤ/2) ⟶ Spec ℤ` therefore gives a group scheme that is not flat over its
base although its identity component is.

## Main definitions

* `Stacks.Examples.DisjointDouble.total`: the disjoint union of the base and `X`, over the base.
* `Stacks.Examples.DisjointDouble.xorGroupPresentation`,
  `Stacks.Examples.DisjointDouble.grpObj`: its group law and the resulting group object.

## Main results

* `Stacks.Examples.exists_groupScheme_flat_identityComponent_not_flat`: the example.

## Implementation notes

The identity component is exhibited as a clopen subscheme containing precisely the image of the
identity section, whose fibre over every point of the base is connected — hence it is the
identity component in every fibre — and whose restricted structure morphism is flat.

The fibre square of the disjoint union over the base decomposes as the disjoint union of the four
fibre products of summands, which is what turns a multiplication defined summand by summand into
a morphism on the whole square.

## References

* [Stacks Project, Tag 06RK](https://stacks.math.columbia.edu/tag/06RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace Stacks.Examples.DisjointDouble

open Stacks.Examples

variable {S X : Scheme.{u}}

/-- The summand of the disjoint union labelled by a boolean: `X` for `true` and the base for
`false`. -/
public abbrev piece (S X : Scheme.{u}) (b : Bool) : Scheme.{u} := if b then X else S

/-- The structure morphism of a summand: the given morphism on `X`, the identity on the base. -/
public def pieceMap (i : X ⟶ S) (b : Bool) : piece S X b ⟶ S :=
  match b with
  | true => i
  | false => 𝟙 S

/-- The disjoint union of the base and `X`, as a scheme over the base. -/
public noncomputable abbrev total (i : X ⟶ S) : CategoryTheory.Over S :=
  Over.mk (Sigma.desc (pieceMap i))

/-- A summand, as a scheme over the base. -/
public abbrev part (i : X ⟶ S) (b : Bool) : CategoryTheory.Over S := Over.mk (pieceMap i b)

/-- The inclusion of a summand into the disjoint union. -/
public noncomputable def partHom (i : X ⟶ S) (b : Bool) : part i b ⟶ total i :=
  Over.homMk (Sigma.ι (piece S X) b) (by simp)

/-- Each summand is a subobject of the base as soon as `X` is. -/
public lemma mono_pieceMap (i : X ⟶ S) [Mono i] (b : Bool) : Mono (pieceMap i b) := by
  cases b
  · exact inferInstanceAs (Mono (𝟙 S))
  · exact inferInstanceAs (Mono i)

/-- Any two morphisms from a fixed scheme over the base into one summand agree. -/
public lemma part_hom_ext (i : X ⟶ S) [Mono i] {T : CategoryTheory.Over S} (b : Bool)
    (f g : T ⟶ part i b) : f = g := by
  have := mono_pieceMap i b
  exact Over.OverMorphism.ext ((cancel_mono (pieceMap i b)).mp (f.w.trans g.w.symm))

/-- The product of two morphisms into summands, landing in the summand labelled by the `xor` of
the labels: the label `false` is neutral and two equal labels cancel. -/
public def partMul (i : X ⟶ S) {T : CategoryTheory.Over S} (b c : Bool)
    (f : T ⟶ part i b) (g : T ⟶ part i c) : T ⟶ part i (b ^^ c) := by
  cases b <;> cases c
  · exact f
  · exact g
  · exact f
  · exact Over.homMk T.hom (by change T.hom ≫ 𝟙 S = T.hom; simp)

/-- The summand of the fibre square of the disjoint union indexed by a pair of labels. -/
public noncomputable abbrev pairPiece (i : X ⟶ S) (b c : Bool) : Scheme.{u} :=
  pullback (pieceMap i b) (pieceMap i c)

/-- A summand of the fibre square, as a scheme over the base. -/
public noncomputable abbrev pairOver (i : X ⟶ S) (b c : Bool) : CategoryTheory.Over S :=
  Over.mk (pullback.fst (pieceMap i b) (pieceMap i c) ≫ pieceMap i b)

/-- The first projection of a summand of the fibre square. -/
public noncomputable def pairFst (i : X ⟶ S) (b c : Bool) : pairOver i b c ⟶ part i b :=
  Over.homMk (pullback.fst _ _)

/-- The second projection of a summand of the fibre square. -/
public noncomputable def pairSnd (i : X ⟶ S) (b c : Bool) : pairOver i b c ⟶ part i c :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

/-- The inclusion of a summand of the fibre square into the fibre square. -/
public noncomputable def pairHom (i : X ⟶ S) (b c : Bool) :
    pairPiece i b c ⟶ pullback (total i).hom (total i).hom :=
  pullback.map _ _ _ _ (Sigma.ι (piece S X) b) (Sigma.ι (piece S X) c) (𝟙 S)
    (by simp) (by simp)

/-- The inclusion of a summand of the fibre square followed by the first projection is the first
projection of the summand followed by the inclusion of its first factor. -/
public lemma pairHom_comp_fst (i : X ⟶ S) (b c : Bool) :
    pairHom i b c ≫ pullback.fst (total i).hom (total i).hom =
      pullback.fst (pieceMap i b) (pieceMap i c) ≫ Sigma.ι (piece S X) b :=
  pullback.lift_fst _ _ _

/-- The inclusion of a summand of the fibre square followed by the second projection is the second
projection of the summand followed by the inclusion of its second factor. -/
public lemma pairHom_comp_snd (i : X ⟶ S) (b c : Bool) :
    pairHom i b c ≫ pullback.snd (total i).hom (total i).hom =
      pullback.snd (pieceMap i b) (pieceMap i c) ≫ Sigma.ι (piece S X) c :=
  pullback.lift_snd _ _ _

/-- The fibre square of the disjoint union, presented as the disjoint union of the four fibre
products of summands. -/
public noncomputable def pairDesc (i : X ⟶ S) :
    (∐ fun p : Bool × Bool => pairPiece i p.1 p.2) ⟶
      pullback (total i).hom (total i).hom :=
  Sigma.desc fun p => pairHom i p.1 p.2

/-- The fibre square of the disjoint union is the disjoint union of the four fibre products of
summands. -/
public instance isIso_pairDesc (i : X ⟶ S) : IsIso (pairDesc i) := by
  dsimp [pairDesc, pairHom, pairPiece]
  infer_instance

/-- On the summand indexed by `(b, c)`, `pairDesc` is the inclusion `pairHom i b c`. -/
public lemma sigmaι_comp_pairDesc (i : X ⟶ S) (b c : Bool) :
    Sigma.ι (fun p : Bool × Bool => pairPiece i p.1 p.2) (b, c) ≫ pairDesc i =
      pairHom i b c :=
  Sigma.ι_desc _ _

/-- The inclusion of a summand followed by the structure morphism of the disjoint union is the
structure morphism of the summand. -/
private theorem sigmaι_comp_total_hom (i : X ⟶ S) (b : Bool) :
    Sigma.ι (piece S X) b ≫ (total i).hom = pieceMap i b :=
  Sigma.ι_desc _ _

/-- The multiplication of the group law on a summand of the fibre square. -/
public noncomputable def pairMul (i : X ⟶ S) [Mono i] (b c : Bool) :
    pairOver i b c ⟶ total i :=
  partMul i b c (pairFst i b c) (pairSnd i b c) ≫ partHom i (b ^^ c)

/-- The multiplication of the group law, as a morphism out of the fibre square. -/
public noncomputable def mulOnPullback (i : X ⟶ S) [Mono i] :
    pullback (total i).hom (total i).hom ⟶ (total i).left :=
  inv (pairDesc i) ≫ Sigma.desc fun p : Bool × Bool => (pairMul i p.1 p.2).left

/-- On the summand of the fibre square indexed by `(b, c)`, the multiplication is
`pairMul i b c`. -/
public lemma pairHom_comp_mulOnPullback (i : X ⟶ S) [Mono i] (b c : Bool) :
    pairHom i b c ≫ mulOnPullback i = (pairMul i b c).left := by
  rw [← sigmaι_comp_pairDesc i b c, mulOnPullback, Category.assoc, IsIso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

/-- The multiplication on the fibre square is a morphism over the base. -/
public lemma mulOnPullback_comp_hom (i : X ⟶ S) [Mono i] :
    mulOnPullback i ≫ (total i).hom =
      pullback.fst (total i).hom (total i).hom ≫ (total i).hom := by
  rw [← cancel_epi (pairDesc i)]
  refine Sigma.hom_ext _ _ fun ⟨b, c⟩ => ?_
  have hlhs : Sigma.ι (fun q : Bool × Bool => pairPiece i q.1 q.2) (b, c) ≫
      pairDesc i ≫ mulOnPullback i ≫ (total i).hom =
      pullback.fst (pieceMap i b) (pieceMap i c) ≫ pieceMap i b := by
    rw [← Category.assoc, ← Category.assoc, sigmaι_comp_pairDesc, pairHom_comp_mulOnPullback]
    exact (pairMul i b c).w
  have hrhs : Sigma.ι (fun q : Bool × Bool => pairPiece i q.1 q.2) (b, c) ≫
      pairDesc i ≫ pullback.fst (total i).hom (total i).hom ≫ (total i).hom =
      pullback.fst (pieceMap i b) (pieceMap i c) ≫ pieceMap i b := by
    rw [← Category.assoc, ← Category.assoc, sigmaι_comp_pairDesc, pairHom_comp_fst,
      Category.assoc, sigmaι_comp_total_hom]
  exact hlhs.trans hrhs.symm

/-- The multiplication of the group law on the disjoint union. -/
public noncomputable def mul (i : X ⟶ S) [Mono i] : total i ⊗ total i ⟶ total i :=
  Over.homMk (tensorLeftToPullback (total i) (total i) ≫ mulOnPullback i) (by
    rw [Category.assoc, mulOnPullback_comp_hom, ← Category.assoc,
      tensorLeftToPullback_comp_fst]
    exact (fst (total i) (total i)).w)

/-- The product of two morphisms landing in the summands labelled `b` and `c` lands in the summand
labelled `b ^^ c`, where it is `partMul i b c`. -/
public lemma lift_partHom_comp_mul (i : X ⟶ S) [Mono i] {T : CategoryTheory.Over S} (b c : Bool)
    (f : T ⟶ part i b) (g : T ⟶ part i c) :
    lift (f ≫ partHom i b) (g ≫ partHom i c) ≫ mul i =
      partMul i b c f g ≫ partHom i (b ^^ c) := by
  have hcond : f.left ≫ pieceMap i b = g.left ≫ pieceMap i c := f.w.trans g.w.symm
  have hL : pullback.lift f.left g.left hcond ≫ (pairOver i b c).hom = T.hom := by
    change pullback.lift f.left g.left hcond ≫
      (pullback.fst (pieceMap i b) (pieceMap i c) ≫ pieceMap i b) = T.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact f.w
  have hstep : (lift (f ≫ partHom i b) (g ≫ partHom i c)).left ≫
      tensorLeftToPullback (total i) (total i) = pullback.lift f.left g.left hcond ≫
        pairHom i b c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, tensorLeftToPullback_comp_fst, ← Over.comp_left, lift_fst,
        Category.assoc, pairHom_comp_fst, ← Category.assoc, pullback.lift_fst, Over.comp_left]
      rfl
    · rw [Category.assoc, tensorLeftToPullback_comp_snd, ← Over.comp_left, lift_snd,
        Category.assoc, pairHom_comp_snd, ← Category.assoc, pullback.lift_snd, Over.comp_left]
      rfl
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, show (mul i).left =
      tensorLeftToPullback (total i) (total i) ≫ mulOnPullback i from rfl, ← Category.assoc,
    hstep, Category.assoc, pairHom_comp_mulOnPullback]
  have hl : (Over.homMk (pullback.lift f.left g.left hcond) hL : T ⟶ pairOver i b c) ≫
      pairMul i b c = partMul i b c f g ≫ partHom i (b ^^ c) := by
    rw [pairMul, ← Category.assoc]
    exact congrArg (· ≫ partHom i (b ^^ c)) (part_hom_ext i _ _ _)
  exact congrArg CommaMorphism.left hl

/-- Two morphisms out of a scheme over the base agree once they agree after restricting to the
preimage of either summand. -/
public lemma total_hom_ext (i : X ⟶ S) {T Z : CategoryTheory.Over S} (f : T ⟶ total i)
    (g h : T ⟶ Z)
    (H : ∀ (b : Bool) (V : CategoryTheory.Over S) (a : V ⟶ T) (t : V ⟶ part i b),
      a ≫ f = t ≫ partHom i b → a ≫ g = a ≫ h) : g = h := by
  refine Over.OverMorphism.ext ?_
  have hπ : IsIso (Sigma.desc fun b => Sigma.ι (piece S X) b) := by
    rw [show (Sigma.desc fun b => Sigma.ι (piece S X) b) = 𝟙 _ from
      Sigma.hom_ext _ _ fun b => by simp]
    infer_instance
  have := FinitaryPreExtensive.isIso_sigmaDesc_fst
    (fun b => Sigma.ι (piece S X) b) f.left hπ
  refine (cancel_epi (Sigma.desc fun b => pullback.fst f.left (Sigma.ι (piece S X) b))).mp ?_
  refine Sigma.hom_ext _ _ fun b => ?_
  simp only [Sigma.ι_desc_assoc]
  have ht : pullback.snd f.left (Sigma.ι (piece S X) b) ≫ (part i b).hom =
      (Over.mk (pullback.fst f.left (Sigma.ι (piece S X) b) ≫ T.hom)).hom := by
    change pullback.snd f.left (Sigma.ι (piece S X) b) ≫ pieceMap i b =
      pullback.fst f.left (Sigma.ι (piece S X) b) ≫ T.hom
    rw [← f.w, ← Category.assoc, pullback.condition, Category.assoc, sigmaι_comp_total_hom]
  exact congrArg CommaMorphism.left
    (H b (Over.mk (pullback.fst f.left (Sigma.ι (piece S X) b) ≫ T.hom))
      (Over.homMk (pullback.fst _ _) rfl) (Over.homMk (pullback.snd _ _) ht)
      (Over.OverMorphism.ext pullback.condition))

/-- The presentation of the group law on the disjoint union: the two summands are the two pieces,
and multiplication adds their labels modulo two. -/
public noncomputable def xorGroupPresentation (i : X ⟶ S) [Mono i] : XorGroupPresentation S where
  carrier := total i
  part := part i
  mono_part_hom := mono_pieceMap i
  partHom := partHom i
  partUnit T := Over.homMk T.hom (by change T.hom ≫ 𝟙 S = T.hom; simp)
  partMul := partMul i
  mul := mul i
  lift_partHom_comp_mul := fun b c f g => lift_partHom_comp_mul i b c f g
  hom_ext := fun f g h H => total_hom_ext i f g h H

/-- The group object over the base carried by the disjoint union. -/
@[instance_reducible]
public noncomputable def grpObj (i : X ⟶ S) [Mono i] : GrpObj (total i) :=
  (xorGroupPresentation i).grpObj

/-- The identity section of the group law is the inclusion of the summand labelled `false`. -/
public lemma one_left (i : X ⟶ S) [Mono i] :
    letI := grpObj i
    (η[total i]).left = Sigma.ι (piece S X) false := by
  let := grpObj i
  rw [show (η[total i]).left =
    (𝟙_ (CategoryTheory.Over S)).hom ≫ Sigma.ι (piece S X) false from rfl,
    Over.tensorUnit_hom]
  exact Category.id_comp _

/-- The disjoint union is flat over the base only if `X` is. -/
public lemma not_flat_total (i : X ⟶ S) (hi : ¬ Flat i) : ¬ Flat (total i).hom := by
  intro h
  have hcomp : Flat (Sigma.ι (piece S X) true ≫ (total i).hom) := inferInstance
  exact hi (by simpa [pieceMap] using hcomp)

/-- The fibre of the identity section over a point of the base is a single point, hence
connected. -/
public lemma isConnected_fibre_range_section {S G : Scheme.{u}}
    (p : G ⟶ S) (e : S ⟶ G) (he : e ≫ p = 𝟙 S) (s : S) :
    _root_.IsConnected {g : {g : G // p g = s} | g.1 ∈ Set.range e} := by
  have hs (t : S) : p (e t) = t := by
    simpa using congrArg (fun f : S ⟶ S ↦ f t) he
  have hset : {g : {g : G // p g = s} | g.1 ∈ Set.range e} = {(⟨e s, hs s⟩ :
      {g : G // p g = s})} := by
    ext g
    constructor
    · rintro ⟨t, ht⟩
      obtain rfl : t = s := by
        rw [← hs t, ht]
        exact g.property
      exact Set.mem_singleton_iff.mpr (Subtype.ext ht.symm)
    · rintro rfl
      exact ⟨s, rfl⟩
  rw [hset]
  exact isConnected_singleton

/-- The summand labelled `false` is a closed and open subscheme of the disjoint union, flat over
the base, equal to the image of the identity section, and connected in every fibre: it is the
identity component. -/
public lemma identityComponent (i : X ⟶ S) [Mono i] :
    letI := grpObj i
    ∃ U : (total i).left.Opens,
      Flat (U.ι ≫ (total i).hom) ∧
        IsClosed (U : Set (total i).left) ∧
          Set.range (η[total i]).left = (U : Set (total i).left) ∧
            ∀ s : S, _root_.IsConnected
              {g : {g : (total i).left // (total i).hom g = s} |
                g.1 ∈ (U : Set (total i).left)} := by
  let := grpObj i
  let e : S ⟶ (total i).left := Sigma.ι (piece S X) false
  have he : e ≫ (total i).hom = 𝟙 S := sigmaι_comp_total_hom i false
  refine ⟨e.opensRange, ?_, ?_, ?_, ?_⟩
  · rw [show e.opensRange.ι ≫ (total i).hom = e.isoOpensRange.inv by
      rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, he, Category.comp_id]]
    infer_instance
  · have hset : (Set.range e)ᶜ = Set.range (Sigma.ι (piece S X) true) := by
      ext x
      refine ⟨fun hx ↦ ?_, fun ⟨t, ht⟩ ⟨s, hs⟩ ↦ Bool.false_ne_true (congrArg Sigma.fst
        ((sigmaι_eq_iff (piece S X) false true s t).mp (hs.trans ht.symm)))⟩
      have hx' : x ∈ ⨆ b, (Sigma.ι (piece S X) b).opensRange :=
        (sigmaOpenCover (piece S X)).iSup_opensRange.symm ▸ trivial
      obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      cases b
      · exact (hx hb).elim
      · exact hb
    exact isOpen_compl_iff.mp (hset ▸ IsOpenImmersion.isOpen_range _)
  · rw [one_left i]
    simp [e]
  · exact isConnected_fibre_range_section (total i).hom e he

end Stacks.Examples.DisjointDouble

namespace Stacks.Examples

open Stacks.Examples.DisjointDouble

/-- **Stacks Project, Tag 06RK.** A group scheme can fail to be flat over its base even when its
identity component is flat over the base. -/
@[stacks 06RK, ega "IV 17.12.8" "non-flat example"]
public theorem exists_groupScheme_flat_identityComponent_not_flat :
    ∃ (S : Scheme.{u}) (G : CategoryTheory.Over S) (hG : GrpObj G),
      letI : GrpObj G := hG
      ¬ Flat G.hom ∧
        ∃ U : G.left.Opens,
          Flat (U.ι ≫ G.hom) ∧
            IsClosed (U : Set G.left) ∧
              Set.range (η[G]).left = (U : Set G.left) ∧
                ∀ s : S,
                  _root_.IsConnected {g : {g : G.left // G.hom g = s} |
                    (g.1 : G.left) ∈ (U : Set G.left)} := by
  let f : ULift.{u} ℤ →+* ULift.{u} (ZMod 2) := RingHom.ulift (Int.castRingHom (ZMod 2))
  let i := Spec.map (CommRingCat.ofHom f)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective x.down
    exact ⟨⟨n⟩, ULift.ext _ _ hn⟩
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ hf
  have hi : ¬ Flat i := by
    rw [Flat.SpecMap_iff]
    exact fun h ↦ Stacks.ChangeOfRings.not_flat_intCastRingHom_zmodTwo (RingHom.Flat.ulift_iff.mp h)
  exact ⟨_, total i, grpObj i, not_flat_total i hi, identityComponent i⟩

end Stacks.Examples

end

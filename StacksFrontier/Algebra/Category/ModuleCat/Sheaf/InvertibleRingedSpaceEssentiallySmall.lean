module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.EssentiallySmall.Invertible
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall

/-!
# The invertible modules on a ringed space form a set

Let `(X, 𝒪_X)` be a ringed space, with the sections of the structure sheaf in `Type u` and the
underlying space in `Type w`, and call a sheaf `L` of `𝒪_X`-modules *invertible* when tensoring
by it is an equivalence of the category of sheaves of `𝒪_X`-modules (Tag 01CS). This file proves
Stacks Tag 01CW: there is a *set* of invertible modules, of size `max u w`, such that every
invertible module on `X` is isomorphic to exactly one of its members. Equivalently, the
invertible modules form an essentially small class at `max u w`; thinning such a class to one
representative per isomorphism class gives a family that is moreover pairwise non-isomorphic, so
that the isomorphism class of a member is determined by its index.

## Main results

* `AlgebraicGeometry.SheafOfModules.essentiallySmall_isInvertible`: the invertible sheaves of
  modules on a ringed space form an essentially small class at `max u w`.
* `AlgebraicGeometry.SheafOfModules.exists_unique_representative_isInvertible`: there is a family
  of invertible modules, indexed by a type of size `max u w`, which are pairwise non-isomorphic
  and to exactly one of which every invertible module on the space is isomorphic.

## Implementation notes

The source's set containing exactly one representative of every isomorphism class is obtained in
two steps. Essential smallness of the invertible-object property gives a small subclass meeting
every isomorphism class, which is the statement that the isomorphism classes form a set of that
size; quotienting such a subclass by the relation "is isomorphic to" and taking one representative
of each class then removes the repetitions. The structure sheaf is regarded as a sheaf of
not-necessarily-commutative rings by forgetting commutativity, because that is what indexes
`SheafOfModules`. The two universes are kept independent and the bound is `max u w`; smallness in
the universe of all module sheaves would not express the source's boundedness claim.

The proof splits on whether the lattice of opens of `X` is `u`-small.

If it is, the site `(Opens X, Opens.grothendieckTopology X)` is essentially small at `u`, so it
admits sheafification for `AddCommGrpCat.{u}` and its class of local isomorphisms is the class
of locally bijective maps. Those are the only two hypotheses of the ringed-site statement
`Stacks.SheafOfModules.essentiallySmall_isInvertible_algebraicGeometry` (Tag 040B), whose bound
`max u' v' w'` for a site `C : Type u'` with morphisms in `Type v'` and sections in `Type w'`
becomes `max u w` here, since `Opens X : Type w` is a preorder category with morphisms in
`Type w`. So on a ringed space Tag 01CW is Tag 040B once the smallness of the site is known, and
no separate local-triviality or gluing argument is needed.

If the lattice of opens is not `u`-small, then `Cardinal.{u}` is itself `max u w`-small, hence
every module of sections has a representative of its isomorphism class among the modules carried
by the out-types of cardinals, and a presheaf of modules is determined by its restriction maps
once its values are fixed. So the whole category of presheaves of modules over the structure
sheaf is essentially small at `max u w`, and therefore so is the category of sheaves of modules,
the forgetful functor being fully faithful. No selection among invertible modules is needed in
this branch.

## References

* [Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u v w a b c c'

namespace AlgebraicGeometry.SheafOfModules

/-- Forgetting commutativity preserves all existing limits, with the shape of the limit in a
universe independent of the universe of the rings: a diagram of commutative rings whose limit
exists has small sections, so the diagram of underlying rings has small sections too and its
limit, created by the forgetful functor to types, exists and is computed sectionwise. -/
local instance preservesLimitsOfSize_forget₂_commRingCat_ringCat :
    PreservesLimitsOfSize.{v, w} (forget₂ CommRingCat.{u} RingCat.{u}) where
  preservesLimitsOfShape := fun {J} _ =>
    { preservesLimit := fun {F} =>
        { preserves := fun {c} hc => by
            have : HasLimit (F ⋙ forget CommRingCat.{u}) :=
              ⟨_, isLimitOfPreserves (forget CommRingCat.{u}) hc⟩
            have hs : Small.{u} (F ⋙ forget CommRingCat.{u}).sections :=
              (Types.hasLimit_iff_small_sections _).mp inferInstance
            have : Small.{u} ((F ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⋙
              forget RingCat.{u}).sections := hs
            exact (preservesLimit_of_createsLimit_and_hasLimit F
              (forget₂ CommRingCat.{u} RingCat.{u})).preserves hc } }

/-- Essential smallness of an object property transports up a universe inequality. -/
private theorem essentiallySmall_trans_univLE {C : Type c} [Category.{c'} C]
    {P : ObjectProperty C} [UnivLE.{a, b}] [ObjectProperty.EssentiallySmall.{a} P] :
    ObjectProperty.EssentiallySmall.{b} P := by
  obtain ⟨Q, hQ, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P
  exact ⟨Q, hQ.trans_univLE (Subtype Q), hPQ⟩

/-- **Stacks Project, Tag 01CW.** The invertible sheaves of modules over the structure sheaf of
a ringed space have only a set of isomorphism classes: there is a set of invertible modules, of
size `max u w`, meeting every isomorphism class of invertible modules on the space. -/
@[stacks 01CW]
theorem essentiallySmall_isInvertible (X : RingedSpace.{u, w}) :
    ObjectProperty.EssentiallySmall.{max u w}
      (AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf)) := by
  classical
  by_cases hsmall : Small.{u} (Opens X)
  · have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{w, u, w, u + 1, u} _ _
    have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{w, u, w, u + 1, u} _
    exact Stacks.SheafOfModules.essentiallySmall_isInvertible_algebraicGeometry _ _
  · have : Small.{max w u} Cardinal.{u} :=
      CardinalGenerated.small_cardinal_of_not_small (Opens X) hsmall
    let R : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
      Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf)
    have : ObjectProperty.EssentiallySmall.{max w u}
        (⊤ : ObjectProperty (PresheafOfModules.{u} R.obj)) :=
      CardinalGenerated.essentiallySmall_presheaf_of_small_cardinal R.obj
    have : EssentiallySmall.{max w u} (PresheafOfModules.{u} R.obj) :=
      (essentiallySmall_iff_objectPropertyEssentiallySmall_top _).mpr inferInstance
    have hSheafSmall : EssentiallySmall.{max w u} (_root_.SheafOfModules.{u} R) :=
      essentiallySmall_of_fully_faithful (_root_.SheafOfModules.forget R)
    have : ObjectProperty.EssentiallySmall.{max w u}
        (⊤ : ObjectProperty (_root_.SheafOfModules.{u} R)) :=
      (essentiallySmall_iff_objectPropertyEssentiallySmall_top _).mp hSheafSmall
    have : UnivLE.{max w u, max u w} := inferInstance
    have hTop : ObjectProperty.EssentiallySmall.{max u w}
        (⊤ : ObjectProperty (_root_.SheafOfModules.{u} R)) :=
      essentiallySmall_trans_univLE (P := ⊤)
    obtain ⟨Q, hQsmall, hQ⟩ := hTop.exists_small_le'
    exact ⟨Q, hQsmall, fun L _ => hQ L trivial⟩

/-- An essentially small class of objects has a transversal of its isomorphism classes: a family
of objects of the class, indexed by a small type, which are pairwise non-isomorphic and to
exactly one of which every object of the class is isomorphic. -/
private theorem exists_unique_representative {C : Type c} [Category.{c'} C]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{a} P] :
    ∃ (I : Type a) (L : I → C), (∀ i, P (L i)) ∧
      (∀ i j, Nonempty (L i ≅ L j) → i = j) ∧
      ∀ M, P M → ∃! i, Nonempty (M ≅ L i) := by
  classical
  obtain ⟨Q, hQsmall, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  have := hQsmall
  let s : Setoid (Subtype Q) :=
    { r := fun A B => Nonempty (A.1 ≅ B.1)
      iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩ }
  have : Small.{a} (Quotient s) := small_of_surjective Quotient.mk_surjective
  let K : Quotient s → C := fun q => q.out.1
  have hKP (q : Quotient s) : P (K q) := hQP _ q.out.2
  have hKinj (q q' : Quotient s) (h : Nonempty (K q ≅ K q')) : q = q' :=
    Quotient.out_equiv_out.1 (show s q.out q'.out from h)
  have hKex (M : C) (hM : P M) : ∃ q, Nonempty (M ≅ K q) := by
    obtain ⟨A, hA, ⟨eA⟩⟩ := hPQ M hM
    exact ⟨Quotient.mk s ⟨A, hA⟩, ⟨eA ≪≫ (Quotient.mk_out (s := s) ⟨A, hA⟩).some.symm⟩⟩
  let k := equivShrink.{a} (Quotient s)
  refine ⟨Shrink.{a} (Quotient s), fun i => K (k.symm i), fun i => hKP _,
    fun i j h => k.symm.injective (hKinj _ _ h), fun M hM => ?_⟩
  obtain ⟨q, hq⟩ := hKex M hM
  refine ⟨k q, ?_, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using hq
  · intro j hj
    refine k.symm.injective (hKinj _ _ ⟨hj.some.symm ≪≫ ?_⟩)
    rw [Equiv.symm_apply_apply]
    exact hq.some

/-- **Stacks Project, Tag 01CW.** There is a family of invertible modules over the structure
sheaf of a ringed space, indexed by a type of size `max u w`, whose members are pairwise
non-isomorphic and such that every invertible module on the space is isomorphic to the member of
exactly one index. -/
@[stacks 01CW "exactly one representative"]
theorem exists_unique_representative_isInvertible (X : RingedSpace.{u, w}) :
    ∃ (I : Type (max u w)) (L : I → _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
          (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
            (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf))),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
            (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) (L i)) ∧
      (∀ i j, Nonempty (L i ≅ L j) → i = j) ∧
      ∀ M, AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
            (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) M →
        ∃! i, Nonempty (M ≅ L i) :=
  have := essentiallySmall_isInvertible X
  exists_unique_representative _

end AlgebraicGeometry.SheafOfModules

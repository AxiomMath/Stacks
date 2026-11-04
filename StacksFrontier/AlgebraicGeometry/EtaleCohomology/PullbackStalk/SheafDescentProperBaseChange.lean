module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.JointlySurjectiveFamilyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentOfBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSheafAdjPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of small étale sheaves from base change

Let `f : X ⟶ Y` be a surjective morphism of a big étale site. This file proves that descent of
sheaves of sets on the small étale sites along `f` is effective — the canonical functor from
sheaves on `Y_étale` to descent data for `{X ⟶ Y}` is an equivalence — as soon as the base change
map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` is invertible for two squares: `f` against itself, and the structure
morphism `X ×_Y X ⟶ Y` against `f`. For `f` proper both are instances of the proper base change
theorem in degree zero, Stacks 0A3U, which gives Stacks 0GF0 with Stacks 0A3U as its single
input.

The argument is not the source's reduction to geometric points but the categorical
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv`: the base change of
`f` along `f` itself is split by the diagonal, which does the work the source's reduction to an
algebraically closed point does. What this file adds is the identification of the base-change
`2`-cells of the pseudofunctor of small étale sheaves with the base change maps.

## Main results

* `AlgebraicGeometry.commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor` and
  `AlgebraicGeometry.mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor`: the
  comparison of the two composite inverse images around a commutative square, and its mate along
  the vertical adjunctions, which is the base change map
  `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`.
* `AlgebraicGeometry.reflectsIsomorphisms_smallEtaleSetPullbackFunctor`: inverse image of sheaves
  of sets along a surjection reflects isomorphisms.
* `smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans`:
  effective descent along a surjection from the two base change maps on the bounded sites.
* **Effective descent along a proper surjection, from Stacks 0A3U**, for sheaves of sets on
  Mathlib's small étale sites:
`smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange`

## Implementation notes

The left adjoints of the pseudofunctor `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`
are the inverse images `AlgebraicGeometry.BigEtaleSite.smallInverseImage` on the nose, so its
adjunctions are `AlgebraicGeometry.BigEtaleSite.smallPullbackAdjunction`. The comparison of
composite inverse images is assembled from its composition constraint, which is
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso` by construction, and its mate along
the vertical adjunctions is turned into a mate along the horizontal ones by
`CategoryTheory.iterated_mateEquiv_conjugateEquiv`, as in
`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`.

Several steps are stated through chosen fibre products and named intermediate equations rather
than by unfolding: identifying a value of the pseudofunctor with the corresponding inverse image
is cheap once, but the kernel re-checks it at every conversion, and long chains of such
conversions exceed its budget.

Nothing here carries a Stacks attribute. The hypothesis of the last theorem is discharged in
`AlgebraicGeometry.smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper`.

## References

* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- The inverse image of the small étale sheaf pseudofunctor along a morphism of a big étale site
is left adjoint to the direct image along it: this is the adjunction
`AlgebraicGeometry.BigEtaleSite.smallPullbackAdjunction`, with its left adjoint spelled as the
value of the pseudofunctor. -/
public abbrev smallEtaleSheafPseudofunctorAdjunction {X Y : B.Scheme} (h : X ⟶ Y) :
    ((smallEtaleSheafInverseImagePseudofunctor B).map h.op.toLoc).toFunctor ⊣
      B.smallPushforward h (Type (u + 1)) :=
  B.smallPullbackAdjunction h (Type (u + 1))

/-- At sheaves of sets of the site's universe, the composition comparison of direct images of
`AlgebraicGeometry.smallEtaleSheafPushforwardCompIso` is
`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso`. -/
private theorem smallEtaleSheafPushforwardCompIso_type (X Y Z : B.Scheme) (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    smallEtaleSheafPushforwardCompIso B X Y Z f g (Type (u + 1)) =
      smallEtaleMorphism_comp_pushforwardIso B X Y Z f g := rfl

/-- Conjugating the identification of the inverse images along two equal morphisms gives the
identification of their direct images. -/
private theorem conjugateEquiv_smallInverseImage_eqToHom {X Y : B.Scheme} {k k' : X ⟶ Y}
    (e : k = k') :
    conjugateEquiv (B.smallPullbackAdjunction k' (Type (u + 1)))
        (B.smallPullbackAdjunction k (Type (u + 1)))
        (eqToHom (congrArg (fun m : X ⟶ Y => B.smallInverseImage m (Type (u + 1))) e)) =
      eqToHom (congrArg (fun m : X ⟶ Y => B.smallPushforward m (Type (u + 1))) e.symm) := by
  subst e
  simp

/-- The composition comparison of the small étale sheaf pseudofunctor, read on functors, is the
inverse of `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. -/
private theorem mapComp_hom_toNatTrans {X Y Z : B.Scheme} (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((smallEtaleSheafInverseImagePseudofunctor B).mapComp k.op.toLoc h.op.toLoc).hom.toNatTrans =
      (smallEtaleMorphism_comp_inverseImageIso B X Y Z h k).inv := by
  rfl

/-- The inverse of the composition comparison of the small étale sheaf pseudofunctor, read on
functors, is `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. -/
private theorem mapComp_inv_toNatTrans {X Y Z : B.Scheme} (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((smallEtaleSheafInverseImagePseudofunctor B).mapComp k.op.toLoc h.op.toLoc).inv.toNatTrans =
      (smallEtaleMorphism_comp_inverseImageIso B X Y Z h k).hom := by
  rfl

/-- The image under the small étale sheaf pseudofunctor of the identification of two equal
morphisms is the identification of their inverse images. -/
private theorem map₂_eqToHom_toNatTrans {X Y : B.Scheme} {k k' : X ⟶ Y} (e : k = k') :
    ((smallEtaleSheafInverseImagePseudofunctor B).map₂
        (eqToHom (congrArg (fun m : X ⟶ Y => m.op.toLoc) e))).toNatTrans =
      eqToHom (congrArg (fun m : X ⟶ Y => B.smallInverseImage m (Type (u + 1))) e) := by
  subst e
  simp only [eqToHom_refl, PrelaxFunctor.map₂_id]
  rfl

/-- The comparison of the two composite inverse images around a commutative square, for the small
étale sheaf pseudofunctor, is the composite of the two composition comparisons of inverse images
with the identification of the inverse images along the two equal composites. -/
public theorem commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor {X X' Y Y' : B.Scheme}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (Pseudofunctor.commSqTwoSquare (smallEtaleSheafInverseImagePseudofunctor B) w :
        _ ⟶ _) =
      (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom ≫
        eqToHom (congrArg (fun m : X' ⟶ Y => B.smallInverseImage m (Type (u + 1))) w.symm) ≫
          (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv := by
  have hw : g.op.toLoc ≫ f'.op.toLoc = f.op.toLoc ≫ i.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc, ← op_comp, ← op_comp, w]
  rw [show Pseudofunctor.commSqTwoSquare (smallEtaleSheafInverseImagePseudofunctor B) w =
      ((smallEtaleSheafInverseImagePseudofunctor B).mapComp g.op.toLoc f'.op.toLoc).inv.toNatTrans ≫
        ((smallEtaleSheafInverseImagePseudofunctor B).map₂ (eqToHom
          (congrArg (fun m : X' ⟶ Y => m.op.toLoc) w.symm))).toNatTrans ≫
        ((smallEtaleSheafInverseImagePseudofunctor B).mapComp f.op.toLoc i.op.toLoc).hom.toNatTrans
      from by
        simp only [Pseudofunctor.commSqTwoSquare, Pseudofunctor.isoMapOfCommSq,
          Pseudofunctor.mapComp', Iso.trans_hom, Iso.symm_hom, PrelaxFunctor.map₂Iso_hom,
          eqToIso.hom, Cat.Hom.toNatIso, Cat.Hom.toNatTrans_comp]
        rfl,
    mapComp_inv_toNatTrans, mapComp_hom_toNatTrans, map₂_eqToHom_toNatTrans B w.symm]
  rfl

/-- **The base-change `2`-cell of the small étale sheaf pseudofunctor is the base change map.**
For a commutative square `i ≫ f = f' ≫ g` of a big étale site, the mate along the two vertical
inverse-image/direct-image adjunctions of the comparison of the two composite inverse images is
the base change comparison `g⁻¹ f_* ⟶ f'_* i⁻¹` of
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, which is built as the mate along the two
horizontal adjunctions of the comparison of the two composite direct images. -/
public theorem mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor
    {X X' Y Y' : B.Scheme}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (mateEquiv (smallEtaleSheafPseudofunctorAdjunction B f)
        (smallEtaleSheafPseudofunctorAdjunction B f')
        (Pseudofunctor.commSqTwoSquare (smallEtaleSheafInverseImagePseudofunctor B) w)).natTrans =
      smallEtaleBaseChangeNatTrans.{u} B i f' f g w := by
  rw [smallEtaleBaseChangeNatTrans]
  refine congrArg TwoSquare.natTrans ((Equiv.eq_symm_apply _).2 ?_)
  refine (iterated_mateEquiv_conjugateEquiv
    (smallEtaleSheafPseudofunctorAdjunction B f) (smallEtaleSheafPseudofunctorAdjunction B f')
    (smallEtaleSheafPseudofunctorAdjunction B g) (smallEtaleSheafPseudofunctorAdjunction B i)
    _).trans ?_
  rw [commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor]
  let A₁ := (B.smallPullbackAdjunction f (Type (u + 1))).comp
    (B.smallPullbackAdjunction i (Type (u + 1)))
  let A₂ := B.smallPullbackAdjunction (f' ≫ g) (Type (u + 1))
  let A₂' := B.smallPullbackAdjunction (i ≫ f) (Type (u + 1))
  let A₃ := (B.smallPullbackAdjunction g (Type (u + 1))).comp
    (B.smallPullbackAdjunction f' (Type (u + 1)))
  have h₁ : conjugateEquiv A₂ A₃ (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom =
      (smallEtaleMorphism_comp_pushforwardIso B X' Y' Y f' g).inv := by
    change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have h₂ : conjugateEquiv A₁ A₂' (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv =
      (smallEtaleMorphism_comp_pushforwardIso B X' X Y i f).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have h₃ := conjugateEquiv_smallInverseImage_eqToHom B w.symm
  change conjugateEquiv A₁ A₃ _ = _
  rw [← conjugateEquiv_comp A₁ A₂ A₃, ← conjugateEquiv_comp A₁ A₂' A₂, h₁, h₂, h₃,
    smallEtaleSheafPushforwardCompIso_type, smallEtaleSheafPushforwardCompIso_type, eqToIso.hom,
    Category.assoc]

/-! ### Inverse image along a surjection reflects isomorphisms -/

/-- **Inverse image of sheaves of sets along a surjective morphism of a big étale site reflects
isomorphisms.** A map `α` whose inverse image is invertible is an epimorphism, because inverse
image along a surjection reflects epimorphisms
(`AlgebraicGeometry.epi_of_epi_smallEtalePullback`), and a monomorphism, because inverse image
along a surjection is faithful (`AlgebraicGeometry.jointlyFaithful_smallEtaleSetPullback` for the
one-member family) and faithful functors reflect monomorphisms; the category of sheaves of sets
is balanced. -/
@[sga "4 VIII 9.1" "special case"]
public theorem reflectsIsomorphisms_smallEtaleSetPullbackFunctor {X Y : B.Scheme} (f : X ⟶ Y)
    (hf : Function.Surjective (B.inclusion.map f).base) :
    (smallEtaleSetPullbackFunctor B f).ReflectsIsomorphisms := by
  have hJ := jointlyFaithful_smallEtaleSetPullback B Y (fun _ : Fin 1 => X) (fun _ => f)
    (fun y => by
      obtain ⟨x, hx⟩ := hf y
      exact ⟨0, x, hx⟩)
  have : (smallEtaleSetPullbackFunctor B f).Faithful :=
    ⟨fun {_ _} {α β} h => hJ.map_injective fun _ => h⟩
  refine ⟨fun {G H} α hα => ?_⟩
  have : Epi α := epi_of_epi_smallEtalePullback B f hf α inferInstance
  have : Mono α := (smallEtaleSetPullbackFunctor B f).mono_of_mono_map inferInstance
  exact isIso_of_mono_of_epi α

/-! ### Effective descent from the two base change maps -/

/-- **Effective descent of small étale sheaves along a surjection, from base change.** Let
`f : X ⟶ Y` be a morphism of a big étale site which is surjective on underlying points, and
suppose that the base change map `g⁻¹ f_* ⟶ f'_* i⁻¹` of sheaves of sets
(`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`) is invertible for the square of `f` against
itself and for the square of the structure morphism `X ×_Y X ⟶ Y` against `f`, the two fibre
products being given as chosen fibre products `XX` and `ZZ`. Then the functor
from sheaves on the small étale site of `Y` to descent data for `{X ⟶ Y}` is an equivalence.

For a proper surjection these two base change maps are invertible by the proper base change
theorem in degree zero, Stacks 0A3U, and the statement is then Stacks 0GF0; for an integral
surjection they are invertible by Stacks 0EYP, and the statement is Stacks 0GEZ. The proof is
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv`: the two
base-change `2`-cells it asks for are the two base change maps, by
`AlgebraicGeometry.mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor`, inverse
image along `f` is left exact, and it reflects isomorphisms because `f` is surjective. -/
public theorem
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans
    {X Y : B.Scheme} (f : X ⟶ Y) (hf : Function.Surjective (B.inclusion.map f).base)
    (XX : ChosenPullback f f) (ZZ : ChosenPullback XX.p f)
    (hβ : ∀ M, IsIso ((smallEtaleBaseChangeNatTrans.{u} B XX.p₁ XX.p₂ f f
      XX.condition).app M))
    (hγ : ∀ N, IsIso ((smallEtaleBaseChangeNatTrans.{u} B ZZ.p₁ ZZ.p₂ XX.p f
      ZZ.condition).app N)) :
    (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence := by
  have : HasEqualizers ((smallEtaleSheafInverseImagePseudofunctor B).obj (.mk (.op Y))) :=
    inferInstanceAs (HasEqualizers (Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))))
  have : HasEqualizers ((smallEtaleSheafInverseImagePseudofunctor B).obj (.mk (.op X))) :=
    inferInstanceAs (HasEqualizers (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))))
  have : PreservesFiniteLimits
      ((smallEtaleSheafInverseImagePseudofunctor B).map f.op.toLoc).toFunctor := by
    have : RepresentablyFlat (smallEtaleBaseChange B f) := flat_of_preservesFiniteLimits _
    exact inferInstanceAs (PreservesFiniteLimits (B.smallInverseImage f (Type (u + 1))))
  have : Functor.ReflectsIsomorphisms
      ((smallEtaleSheafInverseImagePseudofunctor B).map f.op.toLoc).toFunctor :=
    reflectsIsomorphisms_smallEtaleSetPullbackFunctor B f hf
  refine Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv _ f XX ZZ
    (smallEtaleSheafPseudofunctorAdjunction B f) (smallEtaleSheafPseudofunctorAdjunction B XX.p)
    (smallEtaleSheafPseudofunctorAdjunction B XX.p₂)
    (smallEtaleSheafPseudofunctorAdjunction B ZZ.p₂) (fun M => ?_) (fun N => ?_)
  · rw [mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor]
    exact hβ M
  · rw [mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor]
    exact hγ N

/-! ### Proper surjections, from the proper base change theorem -/

/-- **Effective descent of small étale sheaves along a proper surjection, from the proper base
change theorem in degree zero.** Let `f : X ⟶ Y` be a surjective proper morphism of a big étale
site. Granted the conclusion of the proper base change theorem for sheaves of sets, Stacks 0A3U
— for every cartesian square of schemes with proper right-hand side, the base change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` of `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is an isomorphism —
the functor from sheaves on the small étale site of `Y` to descent data for `{X ⟶ Y}` is an
equivalence. This is Stacks 0GF0 with Stacks 0A3U as its single input.

Only two instances of the input are used: the square of `f` against itself and the square of the
proper morphism `X ×_Y X ⟶ Y` against `f`. They are moved from Mathlib's small étale sites to the
bounded ones by
`AlgebraicGeometry.SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange`.
-/
public theorem
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
    {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  let XX := ChosenPullback.ofHasPullback f f
  let ZZ := ChosenPullback.ofHasPullback XX.p f
  have h₁ : IsProper (B.inclusion.map XX.p₁) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (B.inclusion.map_isPullback XX.isPullback.flip) ‹_›
  have hp : IsProper (B.inclusion.map XX.p) := by
    rw [← XX.hp₁, B.inclusion.map_comp]
    infer_instance
  have key : ∀ {W : B.Scheme} (g : W ⟶ Y) (P : ChosenPullback g f),
      IsProper (B.inclusion.map g) →
        ∀ M, IsIso ((smallEtaleBaseChangeNatTrans.{u} B P.p₁ P.p₂ g f P.condition).app M) :=
    fun g P hg M => by
      have := SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange B g f
        P.p₁ P.p₂ P.condition (h0A3U _ _ _ _ (B.inclusion.map_isPullback P.isPullback) hg)
      infer_instance
  exact
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans
      B f (B.inclusion.map f).surjective XX ZZ (key f XX ‹_›) (key XX.p ZZ hp)

end AlgebraicGeometry

end

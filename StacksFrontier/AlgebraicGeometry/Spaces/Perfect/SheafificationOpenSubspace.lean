module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.CategoryTheory.Sites.Sheafification.AlongFullyFaithfulAdjoint

/-!
# Sheafification on the small étale site passes to an open subspace

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `U ⊆ X` be an open
subspace.  This file shows that the four sheafification hypotheses which a statement about
`D(𝒪_X)` carries — existence of sheafification of `AddCommGrpCat`-valued presheaves on the small
étale site of `X` and on each of its slices, and the agreement of the weak equivalences with
the locally bijective morphisms there — hold again on the small étale site of `U` and on each of
*its* slices.

This is what makes the induction principle of Stacks 08GP,
`AlgebraicGeometry.Space.qcqs_induction_on_self`, usable for a property of `D(𝒪_X)`.  That
principle hands the inductive step an elementary distinguished square `(U ⊆ W, V ⟶ W)` and the
property for `U`, `V` and `U ×_W V`; but the property for `U` is only *stated* once `𝒪_U`-modules
are known to be abelian, which is what these instances supply.

## Main results

* `AlgebraicGeometry.Space.smallEtalePostcompFullyFaithful`: postcomposition between small
  étale sites along a monomorphism is fully faithful.
* `AlgebraicGeometry.Space.smallEtalePostcomp_isLeftAdjoint`: postcomposition along a
  relatively representable étale morphism is a left adjoint, base change along it being the
  right adjoint.
* `AlgebraicGeometry.Space.sheafification_smallEtale_openSubspace`: the four hypotheses, on the
  small étale site of an open subspace and on its slices.

## Implementation notes

The global pair is `Stacks.Sites.hasSheafify_of_fullyFaithful_isLeftAdjoint` and its companion,
applied to the postcomposition functor `j : U_étale ⥤ X_étale` of Stacks 03LP.  That functor is
continuous and cocontinuous by Stacks 03LP; the two properties proved here first are the
remaining hypotheses.  Full faithfulness holds because `U ⟶ X` is a monomorphism, so a morphism
of charts over `X` between charts coming from `U` already commutes over `U`.  Being a left
adjoint is checked by exhibiting a terminal object of each costructured arrow category: for a
chart `V ⟶ X`, the chart `V ×_X U ⟶ U` of `U` together with the projection, which is terminal
because the universal property of the fibre product is exactly the required unique
factorization.  Relative representability of `U ⟶ X` is what makes that fibre product a chart.

The slice pair cannot be obtained the same way, because a slice of `U_étale` is not a slice of
`X_étale`.  It is obtained instead from the fact that both are equivalent to the small étale
site of the *underlying chart scheme*: for a chart `V` of `U`, Stacks 04M0
(`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`) identifies `U_étale/V` and
`X_étale/jV` each with the small étale site of `h_V`, compatibly with the topologies.  So the
hypotheses travel from the slice of `X_étale` at `jV` to the chart site and back down to the
slice of `U_étale` at `V`, by the same two transport theorems applied to the two equivalences —
an equivalence being full, faithful and a left adjoint, and being continuous and cocontinuous
through the dense-subsite instances its topology comparison provides.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Postcomposition between small étale sites along a *monomorphism* of algebraic spaces is
fully faithful: a morphism of charts over the target commutes over the source as well, because
the structure morphism can be cancelled. -/
def smallEtalePostcompFullyFaithful {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) [Mono f.hom] :
    (smallEtalePostcomp B S hS f hf).FullyFaithful where
  preimage {_ _} g := ObjectProperty.homMk (CostructuredArrow.homMk g.hom.left (by
    apply (cancel_mono f.hom).1
    simpa [smallEtalePostcomp, Category.assoc] using CostructuredArrow.w g.hom))
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Postcomposition between small étale sites along a relatively representable étale morphism
`f : X ⟶ Y` of algebraic spaces is a left adjoint; the right adjoint is base change along `f`.

The terminal object of the costructured arrow category at a chart `V ⟶ Y` is the chart
`V ×_Y X ⟶ X` of `X` together with the projection to `V`. -/
theorem smallEtalePostcomp_isLeftAdjoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (hr : yoneda.relativelyRepresentable f.hom) :
    (smallEtalePostcomp B S hS f hf).IsLeftAdjoint := by
  let Q := MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)
  let : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  let I := smallEtalePostcomp B S hS f hf
  apply isLeftAdjoint_iff_hasTerminal_costructuredArrow.mpr
  intro V
  -- The fibre product `V ×_Y X`, a chart of `X` by stability of étaleness under base change.
  let W : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (hr.fst V.1.hom),
      MorphismProperty.of_isPullback (hr.isPullback V.1.hom).flip V.2⟩
  let p : I.obj W ⟶ V :=
    ObjectProperty.homMk (CostructuredArrow.homMk (hr.snd V.1.hom) (hr.w V.1.hom).symm)
  apply IsTerminal.hasTerminal (X := CostructuredArrow.mk p)
  refine IsTerminal.ofUniqueHom (fun Z => ?_) (fun Z m => ?_)
  · let l : Z.left ⟶ W := ObjectProperty.homMk
      (CostructuredArrow.homMk
        (hr.lift Z.left.1.hom Z.hom.hom.left Z.hom.hom.w.symm) (hr.lift_fst _ _ _))
    exact CostructuredArrow.homMk l
      (ObjectProperty.hom_ext _ (CostructuredArrow.ext _ _ (hr.lift_snd _ _ _)))
  · exact CostructuredArrow.ext _ _ (ObjectProperty.hom_ext _ (CostructuredArrow.ext _ _
      (hr.hom_ext (m.left.hom.w.trans (hr.lift_fst _ _ _).symm)
        ((congrArg (fun k => k.hom.left) m.w).trans (hr.lift_snd _ _ _).symm))))

/-- Both sheafification hypotheses descend along a full, faithful, continuous and cocontinuous
left adjoint. -/
private theorem hasSheafify_and_wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint
    {C D : Type*} [Category C] [Category D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (I : C ⥤ D) [I.Full] [I.Faithful] [I.IsLeftAdjoint]
    [I.IsContinuous J K] [I.IsCocontinuous J K] [HasSheafify K AddCommGrpCat.{v}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{v}] :
    HasSheafify J AddCommGrpCat.{v} ∧ J.WEqualsLocallyBijective AddCommGrpCat.{v} :=
  ⟨Stacks.Sites.hasSheafify_of_fullyFaithful_isLeftAdjoint J K I AddCommGrpCat.{v},
    Stacks.Sites.wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint J K I AddCommGrpCat.{v}⟩

/-- The sheafification hypotheses of the small étale site of an algebraic space `X` pass to an
open subspace `U ⊆ X`: sheafification of `AddCommGrpCat`-valued presheaves exists on the small
étale site of `U` and on each of its slices, and on each of them the weak equivalences are the
locally bijective morphisms.

The global pair travels along the postcomposition functor `U_étale ⥤ X_étale`, which is fully
faithful (`U ⟶ X` being a monomorphism), a left adjoint, and continuous and cocontinuous by
Stacks 03LP.  The slice pair travels through the small étale site of the underlying chart
scheme, which Stacks 04M0 identifies with the relevant slice on either side. -/
theorem sheafification_smallEtale_openSubspace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    [HasSheafify (SmallEtale.topology B S hS X) AddCommGrpCat.{v}]
    [(SmallEtale.topology B S hS X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [∀ V, HasSheafify ((SmallEtale.topology B S hS X).over V) AddCommGrpCat.{v}]
    [∀ V, ((SmallEtale.topology B S hS X).over V).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    HasSheafify (SmallEtale.topology B S hS U.toFunctor) AddCommGrpCat.{v} ∧
      (SmallEtale.topology B S hS U.toFunctor).WEqualsLocallyBijective AddCommGrpCat.{v} ∧
      (∀ V, HasSheafify ((SmallEtale.topology B S hS U.toFunctor).over V)
        AddCommGrpCat.{v}) ∧
      (∀ V, ((SmallEtale.topology B S hS U.toFunctor).over V).WEqualsLocallyBijective
        AddCommGrpCat.{v}) := by
  let i : (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ := ObjectProperty.homMk U.ι
  have hi : IsEtale B S hS i.hom := isEtale_of_isOpenImmersion B S hS hU.2
  let I := smallEtalePostcomp B S hS i hi
  let : Mono i.hom := inferInstanceAs (Mono U.ι)
  let ff := smallEtalePostcompFullyFaithful B S hS i hi
  let : I.Full := ff.full
  let : I.Faithful := ff.faithful
  let : I.IsLeftAdjoint := smallEtalePostcomp_isLeftAdjoint B S hS i hi hU.2.rep
  let J := SmallEtale.topology B S hS U.toFunctor
  let K := SmallEtale.topology B S hS X
  let : I.IsContinuous J K := smallEtalePostcomp_isContinuous B S hS i hi
  let : I.IsCocontinuous J K := smallEtalePostcomp_isCocontinuous B S hS i hi
  -- The slices, through the small étale site of the underlying chart scheme (Stacks 04M0).
  have hslice (V : SmallEtale B S hS U.toFunctor) :
      HasSheafify (J.over V) AddCommGrpCat.{v} ∧
        (J.over V).WEqualsLocallyBijective AddCommGrpCat.{v} := by
    obtain ⟨eU, heU, _⟩ := smallEtaleEquivalenceOverChart B S hS U.toFunctor hU.1 V
    obtain ⟨eX, heX, _⟩ := smallEtaleEquivalenceOverChart B S hS X hX (I.obj V)
    let L := SmallEtale.topology B S hS (yoneda.obj V.1.left)
    let : eX.functor.IsDenseSubsite L (K.over (I.obj V)) := by
      change eX.functor.IsDenseSubsite
        (SmallEtale.topology B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X).obj (I.obj V)))) _
      rw [← heX]
      infer_instance
    have hXL := hasSheafify_and_wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint.{v}
      (eX.functor.inducedTopology (K.over (I.obj V))) (K.over (I.obj V)) eX.functor
    rw [heX] at hXL
    let : HasSheafify L AddCommGrpCat.{v} := hXL.1
    let : L.WEqualsLocallyBijective AddCommGrpCat.{v} := hXL.2
    let : eU.functor.IsDenseSubsite L (J.over V) := by
      change eU.functor.IsDenseSubsite
        (SmallEtale.topology B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS U.toFunctor).obj V))) _
      rw [← heU]
      infer_instance
    let : eU.symm.inverse.IsDenseSubsite L (J.over V) :=
      inferInstanceAs (eU.functor.IsDenseSubsite L (J.over V))
    let : eU.inverse.IsDenseSubsite (J.over V) L :=
      inferInstanceAs (eU.symm.functor.IsDenseSubsite (J.over V) L)
    exact hasSheafify_and_wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint.{v} (J.over V) L
      eU.inverse
  have hglobal := hasSheafify_and_wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint.{v} J K I
  exact ⟨hglobal.1, hglobal.2, fun V => (hslice V).1, fun V => (hslice V).2⟩

end AlgebraicGeometry.Space

end

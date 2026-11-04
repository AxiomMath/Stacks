module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOfAffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# The stages of a directed colimit, and the charts of the colimit they carry

Let `S` be a scheme contained in a big fppf site `B` and let `E` be a directed system of fppf
sheaves over `S` whose transition morphisms are representable thickenings. Then each colimit
injection `E_i ⟶ colim E` is itself a representable thickening, so the reduction of one stage is
a reduction of the colimit, and the étale lift of Stacks 0DEG carries every affine formal chart
of a stage to a chart of the colimit.

The thickening of the colimit injections is proved twice. The first form,
`isRepresentableThickeningULift_colimitι`, assumes that every scheme-valued point of the colimit
factors through a stage; that assumption is false at a general object of the site. The second,
`isRepresentableThickeningULift_colimitι_of_small`, assumes nothing of the points and instead
asks that the sections of the stages be pointwise `u`-small — which a formal algebraic space
satisfies by Stacks 0AIS, `AlgebraicGeometry.FormalSpace.small_of_isFormalAlgebraicSpace`. It
uses the factorization only at the *quasi-compact* objects, where it is a theorem, and glues the
local representing objects; that gluing needs a size bound, and a thickening carries one because
its represented base changes are closed subschemes of the test object. That is the form the
consumers in `StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpaces` use.

Everything after those two statements is asked of the *colimit injections* only: that each
`E_i ⟶ colim E` be a representable thickening.

The last statement is the chart system that the proof of **Stacks 0GVN** transports. The étale
transport is not what is missing from it: Stacks 0DEG is a full equivalence in this library,
`AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`, so the chart of the
colimit exists, is representable étale over the colimit, has a formal algebraic space for its
base change to every stage, and all of those base changes have the chart's own reduction — a
reduced affine object of the site — for a reduction. Those base changes are therefore *affine*
formal algebraic spaces by **Stacks 0DE8**,
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_iff_isAffine_reduction`, which is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_liftAlongBase` below. What
the chart system still asserts beyond this is that the charts cover each stage, which asks that
local surjectivity descend along a representable thickening and which the library does not
carry in any form. See the documentation of
`StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpaces`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableThickening_of_stageSquares`: a morphism of fppf
  sheaves is a representable thickening as soon as it becomes one after base change along a
  family of morphisms into its target through which every scheme-valued point of that target
  factors. This is the thickening analogue of
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_colimitι`: the colimit
  injections of such a system are representable thickenings.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_colimitι_of_small`: the same
  conclusion with **no** hypothesis on the scheme-valued points of the colimit, asking instead
  only that the sections of the stages be pointwise `u`-small. This is the form the consumers
  use, the factorization over a general object of the site being false.
* `AlgebraicGeometry.FormalSpace.isReduction_comp_colimitι`: hence the reduction of any one
  stage is a reduction of the colimit.
* `AlgebraicGeometry.FormalSpace.exists_isReduction_of_isRepresentableThickening_comp`: a
  reduced object of the site thickening a sheaf thickens every representable thickening of that
  sheaf, and is a reduction of it.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_and_isReduction_pullback_liftAlongBase`:
  the chart of the colimit attached to an affine formal chart of a stage, with its reduction.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_liftAlongBase`: the same
  chart with its base changes recognised as affine formal algebraic spaces, by Stacks 0DE8 —
  everything Stacks 0GVN asks of a chart system except the covering clause.

## Implementation notes

The two stages `E_i` and `E_j` of the system need not be comparable, so the fibre product
`E_i ×_{colim E} E_j` is computed over a common later stage `E_k`, which the directedness of the
index supplies: the colimit injections are monomorphisms, because a filtered colimit of sheaves
along monomorphisms has monomorphic injections
(`CategoryTheory.Sheaf.mono_colimit_ι_of_mono_transition`), and a cartesian square stays
cartesian after composing both legs of its base with a monomorphism
(`AlgebraicGeometry.FormalSpace.isPullback_comp_mono`).

That the reduction of a sheaf is a reduction of each of its representable thickenings is read
off the base change of the thickening along the reduction: that base change is a thickening of
objects of the site whose target is reduced, hence an isomorphism. No formality hypothesis is
needed for it, which is what lets it be applied to the base changes of a chart of the colimit,
none of which is known in advance to be an affine formal algebraic space.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0DE8](https://stacks.math.columbia.edu/tag/0DE8)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0GVL](https://stacks.math.columbia.edu/tag/0GVL)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of fppf sheaves is a representable thickening as soon as it becomes one after
base change along a family of morphisms into its target through which every scheme-valued point
of that target factors.** This is the thickening analogue of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`: a point of the target is
carried into one member of the family, and the base change of the morphism along the point is
then the base change along that point of the corresponding member of the family. -/
theorem isRepresentableThickening_of_stageSquares {Λ : Type*}
    {X Z : FppfSheaf B S hS} {Y W : Λ → FppfSheaf B S hS} (ζ : X ⟶ Z)
    (p : ∀ i, Y i ⟶ X) (a : ∀ i, Y i ⟶ W i) (ψ : ∀ i, W i ⟶ Z)
    (ha : ∀ i, Space.IsRepresentableThickeningULift.{u + 1} B S hS (a i).hom)
    (hsq : ∀ i, IsPullback (p i) (a i) ζ (ψ i))
    (hfac : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (W i).obj), ξ = ξ' ≫ (ψ i).hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS ζ.hom := by
  classical
  have hsqP : ∀ i, IsPullback (p i).hom (a i).hom ζ.hom (ψ i).hom := fun i ↦
    (hsq i).map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  -- every cartesian square over `Z` is a cartesian square over a stage
  have key : ∀ ⦃A C : BigFppfOver B S hS⦄ (g : (uliftYoneda.{u + 1}).obj A ⟶ Z.obj)
      (fst : (uliftYoneda.{u + 1}).obj C ⟶ X.obj) (snd : C ⟶ A),
      IsPullback fst ((uliftYoneda.{u + 1}).map snd) ζ.hom g →
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj A ⟶ (W i).obj)
        (l : (uliftYoneda.{u + 1}).obj C ⟶ (Y i).obj),
        IsPullback l ((uliftYoneda.{u + 1}).map snd) (a i).hom ξ' := by
    intro A C g fst snd hpb
    obtain ⟨i, ξ', hξ⟩ := hfac A g
    subst hξ
    have hw : fst ≫ ζ.hom
        = ((uliftYoneda.{u + 1}).map snd ≫ ξ') ≫ (ψ i).hom := by
      rw [Category.assoc]; exact hpb.w
    refine ⟨i, ξ', (hsqP i).lift fst ((uliftYoneda.{u + 1}).map snd ≫ ξ') hw, ?_⟩
    refine (IsPullback.of_bot (h₂₁ := (a i).hom) ?_ ?_ (hsqP i).flip).flip
    · rw [(hsqP i).lift_fst]
      exact hpb.flip
    · exact ((hsqP i).lift_snd fst ((uliftYoneda.{u + 1}).map snd ≫ ξ') hw).symm
  refine ⟨?_, ?_⟩
  · intro A g
    obtain ⟨i, ξ', hξ⟩ := hfac A g
    refine ⟨(ha i).rep.pullback ξ', (ha i).rep.snd ξ',
      (ha i).rep.fst ξ' ≫ (p i).hom, ?_⟩
    rw [hξ]
    exact (((ha i).rep.isPullback ξ').flip.paste_vert (hsqP i).flip).flip
  · intro A C g fst snd hpb
    obtain ⟨i, ξ', l, hl⟩ := key g fst snd hpb
    exact (ha i).property ξ' l snd hl

attribute [local instance] Sheaf.instHasColimitsOfSize

/-- The base change of a representable thickening of fppf sheaves is a representable thickening. -/
private theorem isRepresentableThickeningULift_of_isPullback {X Y Z W : FppfSheaf B S hS}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (sq : IsPullback f g h k)
    (hk : Space.IsRepresentableThickeningULift.{u + 1} B S hS h.hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS g.hom :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hk

/-- The colimit injections of a directed system along representable thickenings are
monomorphisms. -/
private theorem mono_colimit_ι_of_isRepresentableThickening {Λ : Type (u + 1)} [Preorder Λ]
    [Nonempty Λ] [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) (k : Λ) :
    Mono (colimit.ι E k) :=
  Sheaf.mono_colimit_ι_of_mono_transition E
    (fun _ _ g ↦ mono_of_isRepresentableThickening B S hS (E.map g) (hthick g)) k

/-- A cartesian square over a stage `E_k`, whose first leg is a transition morphism, stays
cartesian after composing both legs with the monomorphism `E_k ⟶ colim E`. -/
private theorem isPullback_colimit_ι_of_isPullback {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {i k : Λ} (hik : i ⟶ k) {P Y : FppfSheaf B S hS} {fst : P ⟶ E.obj i} {snd : P ⟶ Y}
    {g : Y ⟶ E.obj k} (sq : IsPullback fst snd (E.map hik) g) :
    IsPullback fst snd (colimit.ι E i) (g ≫ colimit.ι E k) := by
  have := mono_colimit_ι_of_isRepresentableThickening B S hS E hthick k
  have h := isPullback_comp_mono sq (colimit.ι E k)
  rwa [colimit.w E hik] at h

/-- **The colimit injections of a directed system of fppf sheaves along representable
thickenings are representable thickenings**, provided every scheme-valued point of the colimit
factors through a stage.

Two stages need not be comparable, so the fibre product of `E_i` and `E_j` over the colimit is
computed over a common later stage, which directedness supplies: the injection of that later
stage is a monomorphism, and `AlgebraicGeometry.FormalSpace.isPullback_comp_mono` turns the
cartesian square of the two transition morphisms over it into a cartesian square over the
colimit. -/
theorem isRepresentableThickeningULift_colimitι {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (hfac : ∀ (U : BigFppfOver B S hS)
      (ξ : (uliftYoneda.{u + 1}).obj U ⟶ (colimit E).obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (E.obj i).obj),
        ξ = ξ' ≫ (colimit.ι E i).hom)
    (i : Λ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E i).hom := by
  classical
  -- for every index `j` a common later stage
  choose k hik hjk using fun j : Λ ↦ directed_of (· ≤ ·) i j
  refine isRepresentableThickening_of_stageSquares B S hS (colimit.ι E i)
    (Y := fun j ↦ pullback (E.map (homOfLE (hik j))) (E.map (homOfLE (hjk j))))
    (fun j ↦ pullback.fst _ _) (fun j ↦ pullback.snd _ _) (fun j ↦ colimit.ι E j)
    (fun j ↦ ?_) (fun j ↦ ?_) hfac
  · exact isRepresentableThickeningULift_of_isPullback B S hS
      (IsPullback.of_hasPullback (E.map (homOfLE (hik j))) (E.map (homOfLE (hjk j)))) (hthick _)
  · have h := isPullback_colimit_ι_of_isPullback B S hS E hthick (homOfLE (hik j))
      (IsPullback.of_hasPullback (E.map (homOfLE (hik j))) (E.map (homOfLE (hjk j))))
    rwa [colimit.w E (homOfLE (hjk j))] at h

/-- **The colimit injections of a directed system of fppf sheaves along representable
thickenings are representable thickenings**, with nothing assumed of the scheme-valued points of
the colimit beyond pointwise `u`-smallness of the sections of the stages.

Unlike `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_colimitι` this does not ask
that *every* scheme-valued point of the colimit factor through a stage — a demand which is false
at a general object of the site. It uses only the factorization at a *quasi-compact* object,
`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`, and glues the
resulting local representing objects over the affine opens of an arbitrary test object with
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`. The gluing needs
a size bound on the local representing objects, and a thickening supplies one: the base change of
`E_i ⟶ colim E` along a point of an affine object `U` is, where it is represented, a closed
subscheme of `U`, hence no larger than `U` by Stacks 000R (4) — so the bound holds at the cardinal
`0` and no regularity of the cutoff is needed. Étaleness would bound nothing, which is why the
same route is unavailable for the étale clause of Definition 0AIM.

Two stages need not be comparable, so the point of the colimit and the injection at `i` are both
pushed into a common later stage, which directedness supplies; the injection of that later stage
is a monomorphism, and `AlgebraicGeometry.FormalSpace.isPullback_comp_mono` turns the cartesian
square there into a cartesian square over the colimit. -/
theorem isRepresentableThickeningULift_colimitι_of_small {Λ : Type (u + 1)} [Preorder Λ]
    [Nonempty Λ] [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (hsmall : ∀ i : Λ, FunctorToTypes.Small.{u} (E.obj i).obj)
    (i : Λ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E i).hom := by
  classical
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigFppfOver.toScheme B S hS
  have : FunctorToTypes.Small.{u} (E.obj i).obj := hsmall i
  -- the thickening condition on the transition morphisms, in the sheaf-level rendering
  have hthickS : ∀ ⦃k l : Λ⦄ (g : k ⟶ l),
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u}) T).relative G
        (E.map g) := fun _k _l g ↦
    (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ (E.map g)).mpr (hthick g)
  refine (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ (colimit.ι E i)).mp ?_
  refine CartesianColimit.relative_of_affineBaseChanges' B S hS _
    Stacks.Thickenings.isThickening_isZariskiLocalAtTarget (colimit.ι E i) (κ := 0)
    (Or.inl (Cardinal.aleph0_pos.trans B.aleph0_lt_cutoff)) ?_
  intro U hU ξ
  have : IsAffine (T.obj U) := hU
  -- an affine object of the site is quasi-compact, so the point factors through a stage
  obtain ⟨j, g, hg⟩ :=
    compact_map_factors_through_filtered_colimit E
      (fun _ _ g ↦ mono_of_isRepresentableThickening B S hS (E.map g) (hthick g)) U
      (BigFppfOver.isQuasiCompactObject_of_compactSpace B S hS U inferInstance) ξ
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hξ : (g ≫ E.map (homOfLE hjk)) ≫ colimit.ι E k = ξ := by
    rw [Category.assoc, colimit.w E (homOfLE hjk)]; exact hg
  -- the base change of the transition morphism `E_i ⟶ E_k` along that point is represented
  obtain ⟨V, q, fst, sq⟩ := (hthickS (homOfLE hik)).rep (g ≫ E.map (homOfLE hjk))
  have hq : Stacks.Thickenings.IsThickening (T.map q) :=
    (hthickS (homOfLE hik)).property _ fst q sq
  have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map q) := hq.1
  refine ⟨V, fst, q, ?_, hq, (Scheme.size_le_of_mono_quasiCompact (T.map q)).trans
    (le_max_right _ _)⟩
  -- and it is a base change over the colimit, the injection at `k` being a monomorphism
  have h := isPullback_colimit_ι_of_isPullback B S hS E hthick (homOfLE hik) sq
  rwa [hξ] at h

/-- **The reduction of a stage is a reduction of the colimit.** The inclusion of the reduction
of one stage into the colimit is a composite of two representable thickenings, and a
representable thickening by a reduced algebraic space is a reduction
(`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`). So all the stages
and the colimit have one and the same reduction, which is what the proof of Stacks 0GVN uses
when it transports an affine étale chart of the reduction to every stage.

The hypothesis is that the colimit injections are representable thickenings, which
`AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_colimitι` supplies from the
factorization of every scheme-valued point through a stage, but which is weaker than that
factorization — the factorization is false for an arbitrary object of the site. -/
theorem isReduction_comp_colimitι {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hι : ∀ i : Λ,
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E i).hom)
    {i : Λ} {R : FppfSheaf B S hS} {r : R ⟶ E.obj i}
    (hr : IsReduction B S hS (E.obj i) R r) :
    IsReduction B S hS (colimit E) R (r ≫ colimit.ι E i) :=
  isReduction_of_isRepresentableThickening B S hS _ hr.algebraic hr.reduced
    (isRepresentableThickeningULift_comp B S hS hr.isRepresentableThickening (hι i))

/-- **A reduced object of the site thickening a sheaf thickens every representable thickening
of that sheaf.** Let `a : h_T ⟶ V` be a representable thickening with `T` a reduced object of
the site and let `q : P ⟶ V` be a representable thickening. The base change of `q` along `a` is
a thickening of objects of the site with reduced target, hence an isomorphism, so `a` factors
through `q` by a representable thickening; and that factorization exhibits `h_T` as a reduction
of `P`. This is how the reduction of a sheaf is seen to be the reduction of each of its
representable thickenings, with no formality hypothesis on either. -/
theorem exists_isReduction_of_isRepresentableThickening_comp
    {V P : FppfSheaf B S hS} {T : BigFppfOver B S hS}
    (a : yonedaSheaf B S hS T ⟶ V) (q : P ⟶ V)
    (hTred : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (ha : Space.IsRepresentableThickeningULift.{u + 1} B S hS a.hom)
    (hq : Space.IsRepresentableThickeningULift.{u + 1} B S hS q.hom) :
    ∃ w : yonedaSheaf B S hS T ⟶ P, w ≫ q = a ∧
      Space.IsRepresentableThickeningULift.{u + 1} B S hS w.hom ∧
      IsReduction B S hS P (yonedaSheaf B S hS T) w := by
  obtain ⟨hclosed, hsurj⟩ := hq.property_snd a.hom
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj T) := hTred
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hq.rep.snd a.hom)) := hclosed
  have _ : _root_.AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hq.rep.snd a.hom)) := ⟨hsurj⟩
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map (hq.rep.snd a.hom)) :=
    isIso_of_isClosedImmersion_of_surjective _
  have _ : IsIso (hq.rep.snd a.hom) :=
    isIso_of_reflects_iso (hq.rep.snd a.hom) (BigFppfOver.toScheme B S hS)
  have hsq := hq.rep.isPullback a.hom
  set e : (uliftYoneda.{u + 1}).obj (hq.rep.pullback a.hom) ≅ (yonedaSheaf B S hS T).obj :=
    (uliftYoneda.{u + 1}).mapIso (asIso (hq.rep.snd a.hom)) with he
  -- the base change of `a` along `q`, a representable thickening
  have hfstthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (hq.rep.fst a.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip ha
  have hwthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (e.inv ≫ hq.rep.fst a.hom) :=
    isRepresentableThickeningULift_comp B S hS
      (isRepresentableThickeningULift_of_isIso B S hS e.inv) hfstthick
  refine ⟨⟨e.inv ≫ hq.rep.fst a.hom⟩, ?_, hwthick, ?_⟩
  · refine Sheaf.hom_ext ?_
    show (e.inv ≫ hq.rep.fst a.hom) ≫ q.hom = a.hom
    have hw : hq.rep.fst a.hom ≫ q.hom = e.hom ≫ a.hom := hsq.w
    rw [Category.assoc, hw, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · exact isReduction_yonedaSheaf_of_isRepresentableThickening B S hS T _ hTred hwthick

/-- **The chart of the colimit attached to an affine formal chart of a stage, and what is
missing from it.** Let `E` be a directed system of formal algebraic spaces over `S` whose
colimit injections are representable thickenings,
and let `p : Y ⟶ E_i` be an affine formal algebraic space representably étale over one stage —
one member of the atlas of that stage, as Definition 0AIM provides. The dependent product of
`p` along the colimit injection, which is the étale lift of Stacks 0DEG, is then a sheaf `V`
over the colimit for which:

* `V ⟶ colim E` is representable by algebraic spaces and étale;
* the base change of `V` to *every* stage `E_j` is a formal algebraic space;
* all of those base changes have one and the same reduction, namely the reduction `T` of `Y`,
  which is a reduced **affine** object of the site.

The affineness of those base changes is **Stacks 0DE8**, the affineness of a formal algebraic
space whose reduction is an affine scheme, and it is added to this conclusion in
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_liftAlongBase`. The étale
transport is no part of what either statement grants: Stacks 0DEG is available here as a full
equivalence (`AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`). -/
theorem isRepresentableEtale_and_isReduction_pullback_liftAlongBase
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ j : Λ, IsFormalAlgebraicSpace B S hS (E.obj j))
    (hι : ∀ j : Λ,
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E j).hom)
    {i : Λ} {Y : FppfSheaf B S hS} (p : Y ⟶ E.obj i)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hp : IsRepresentableEtale B S hS p) :
    IsRepresentableEtale B S hS (liftAlongBase B S hS (colimit.ι E i) p) ∧
      ∃ T : BigFppfOver B S hS,
        IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
        ∀ j : Λ,
          IsFormalAlgebraicSpace B S hS
              (pullback (liftAlongBase B S hS (colimit.ι E i) p) (colimit.ι E j)) ∧
            ∃ w : yonedaSheaf B S hS T ⟶
                pullback (liftAlongBase B S hS (colimit.ι E i) p) (colimit.ι E j),
              IsReduction B S hS
                (pullback (liftAlongBase B S hS (colimit.ι E i) p) (colimit.ι E j))
                (yonedaSheaf B S hS T) w := by
  classical
  have hιthick : ∀ j : Λ, Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (colimit.ι E j).hom := hι
  have hinj : ∀ A : BigFppfOver B S hS,
      Function.Injective ((colimit.ι E i).hom.app (Opposite.op A)) := fun A ↦
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_of_isRepresentableThickeningULift B S hS (hιthick i)) (Opposite.op A))
  set v : liftAlong B S hS (colimit.ι E i) p ⟶ colimit E :=
    liftAlongBase B S hS (colimit.ι E i) p with hv
  have hvet : IsRepresentableEtale B S hS v :=
    isRepresentableEtale_liftAlongBase B S hS (hιthick i) hp
  -- the reduction of the affine formal chart `Y`, a reduced affine object of the site
  obtain ⟨T, t, hTred, hTaff, htthick, -⟩ :=
    exists_isReduction_reduced_affine_siteObject_of_isAffineFormal B S hS Y hY
  -- `Y ⟶ V` is a base change of the colimit injection, hence a representable thickening
  have hsectthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (liftAlongSection B S hS hinj (p := p)).hom :=
    isRepresentableThickeningULift_of_isPullback B S hS
      (isPullback_liftAlongSection B S hS hinj (p := p)).flip (hιthick i)
  have hathick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (t ≫ liftAlongSection B S hS hinj (p := p)).hom :=
    isRepresentableThickeningULift_comp B S hS htthick hsectthick
  refine ⟨hvet, T, hTred, hTaff, fun j ↦ ⟨?_, ?_⟩⟩
  · exact isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v (colimit.ι E j)
      (hform j) hvet
  · have hfstthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
        (pullback.fst v (colimit.ι E j)).hom :=
      isRepresentableThickeningULift_of_isPullback B S hS
        (IsPullback.of_hasPullback v (colimit.ι E j)).flip (hιthick j)
    obtain ⟨w, -, -, hwred⟩ := exists_isReduction_of_isRepresentableThickening_comp B S hS
      (t ≫ liftAlongSection B S hS hinj (p := p)) (pullback.fst v (colimit.ι E j)) hTred
      hathick hfstthick
    exact ⟨w, hwred⟩

/-- **The chart of the colimit attached to an affine formal chart of a stage has *affine* formal
base changes to every stage.** This is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_and_isReduction_pullback_liftAlongBase`
with its last clause upgraded by **Stacks 0DE8**: each base change is a formal algebraic space
whose reduction is the sheaf of a reduced *affine* object of the site, which is exactly the
hypothesis of
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_iff_isAffine_reduction`.

Together with the étale clause this is the whole chart system of Stacks 0GVN except the
covering clause: the diagram `j ↦ V ×_{colim E} E_j` has affine formal algebraic spaces for
stages, its transition morphisms are base changes of those of `E` and its projections base
changes of `V ⟶ colim E`. The single hypothesis `h07VS` that Stacks 0DE8 carries here, the
conclusion of Stacks 07VS in the shape `AlgebraicGeometry.FormalSpace.Is07VS` — an algebraic
space receiving a surjective *finite* morphism from an affine scheme of the site is an affine
scheme — is passed through unchanged. It is strictly weaker than the `Is07VT` this once
carried; see `AlgebraicGeometry.FormalSpace.is07VS_of_is07VT`. -/
theorem isAffineFormalAlgebraicSpace_pullback_liftAlongBase
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ j : Λ, IsFormalAlgebraicSpace B S hS (E.obj j))
    (hι : ∀ j : Λ,
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E j).hom)
    {i : Λ} {Y : FppfSheaf B S hS} (p : Y ⟶ E.obj i)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hp : IsRepresentableEtale B S hS p)
    (haff : IsAffineOfSurjectiveClosedImmersion B S hS) :
    IsRepresentableEtale B S hS (liftAlongBase B S hS (colimit.ι E i) p) ∧
      ∀ j : Λ, IsAffineFormalAlgebraicSpace B S hS
        (pullback (liftAlongBase B S hS (colimit.ι E i) p) (colimit.ι E j)) := by
  obtain ⟨hvet, T, hTred, hTaff, hj⟩ :=
    isRepresentableEtale_and_isReduction_pullback_liftAlongBase B S hS E hform hι p hY hp
  refine ⟨hvet, fun j ↦ ?_⟩
  obtain ⟨hjform, w, hwred⟩ := hj j
  exact isAffineFormalAlgebraicSpace_of_isReduction_uliftYoneda_of_isAffine B S hS hjform hwred
    (Iso.refl _) hTaff haff

end AlgebraicGeometry.FormalSpace

end

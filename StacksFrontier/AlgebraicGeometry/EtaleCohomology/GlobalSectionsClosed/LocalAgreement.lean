module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Injectivity
public import StacksFrontier.AlgebraicGeometry.Sites.LocallySurjectiveUnivLE

/-!
# Two global sections with the same pullback to a subscheme agree locally over its image

Let `i : Z ⟶ X` be a morphism of schemes and `F` a sheaf of sets on the small étale site of `X`.
If two global sections of `F` have the same presheaf-level pullback to `Z`, then for every point
`z` of `Z` there is an object of the small étale site of `X` whose image contains `i z` and over
which the two sections agree. Together with
`Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt` this proves the injectivity half
of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF).

The pullback is a left Kan extension along base change followed by sheafification, so the proof
has two halves. Sheafification is locally injective, so the two sections already agree in the
left Kan extension after restriction along a covering family of `Z`; small étale coverings are
detected by the images of the underlying maps, so one member of that family hits the chosen
point. Over that member the left Kan extension is a *filtered* colimit — base change between
small étale sites preserves finite limits, hence is representably flat — and equality in a
filtered colimit of sets is witnessed at a single object of the indexing category. That object
is an object `W` of the small étale site of `X` together with a morphism from the member of the
covering family to `W ×_X Z`, and it is over `W` that the two sections agree; following that
morphism through the fibre product puts `i z` in the image of `W`.

## Main results

* `Stacks.EtaleCohomology.surjective_terminal_hom` — the final object of a small étale site maps
  onto the base.
* `Stacks.EtaleCohomology.equalizerSieve_mem_of_toSheafify_eq` — two sections of a presheaf on a
  small étale site with the same image in the sheafification agree on a covering.
* `Stacks.EtaleCohomology.exists_globalSectionEqAt_of_lan_eq` — equality of two sections after
  the unit of the left Kan extension and one restriction is witnessed over a single object.
* `Stacks.EtaleCohomology.exists_globalSectionEqAt_of_pullback_eq` — the statement above.
* `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionPullback_of_zariski` and
  `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_of_zariskiSurjective` — the
  injectivity half of Tag 09ZF under hypothesis (1).

## Implementation notes

Preservation of finite limits by `smallEtaleBaseChange`, and its representable flatness, are
imported from `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous`; the
individual limit shapes follow from finite-limit preservation by
`CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`.

Local injectivity of the sheafification map is not available from Mathlib here: Mathlib's
instances for it constrain the coefficient category to the universe of the site, and étale
cohomology is written with coefficients in `Type (max (u + 1) v)` for a free `v`; the same
constraint is the reason the `HasSheafify` hypotheses of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/HenselianPairRestriction.lean` are hypotheses. The
statement under the weaker
hypothesis `UnivLE.{max z w, v}` is `Stacks.Sheafification.isLocallyInjective_toPlus_type`, and the
instance below is that theorem applied to the small étale topology; the small étale site has
objects in `Type (u + 1)` and morphisms in `Type u`, so the hypothesis it needs is
`UnivLE.{u + 1, max (u + 1) v}`, which holds. The sheafification map of the adjunction is the
twofold plus map composed with `CategoryTheory.plusPlusIsoSheafify`, whose components are
bijections, and that last step is carried out here.

The type of a point of `(smallEtaleBaseChange i).obj W` mentions `smallEtaleBaseChange`, which
does not unfold at `implicit` transparency, so the computation with
`CategoryTheory.Limits.pullback.condition` is done in term mode: `rw` reports that the goal is
not type-correct at that transparency level, while `Eq.trans` and `exact` cross it.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.GrothendieckTopology.Plus

universe u v

namespace Stacks.EtaleCohomology

/-- The final object of the small étale site of `S` maps onto `S`: it is isomorphic to `S` with
its identity morphism, so its structure morphism is an isomorphism. -/
public theorem surjective_terminal_hom (S : Scheme.{u}) :
    Function.Surjective ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S).base := by
  have hiso : IsIso ((Scheme.Etale.mk (𝟙 S)).hom : S ⟶ S) := inferInstanceAs (IsIso (𝟙 S))
  let e : terminal S.Etale ≅ Scheme.Etale.mk (𝟙 S) :=
    terminalIsTerminal.uniqueUpToIso (isTerminalOfIsIsoHom _)
  have hleft : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Scheme.Etale.forget S ⋙ CategoryTheory.Over.forget S).map e.hom))
  have heq : ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S) = e.hom.left :=
    (MorphismProperty.Over.w e.hom).symm.trans (Category.comp_id _)
  rw [heq]
  exact (Scheme.Hom.homeomorph e.hom.left).surjective

section Sheafify

variable {Z : Scheme.{u}}

/-- The unit of the plus construction on the small étale site is locally injective, at the
coefficient universe of étale cohomology. -/
public instance isLocallyInjective_smallEtaleToPlus
    (P : Z.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology Z)
      ((Scheme.smallEtaleTopology Z).toPlus P) :=
  Stacks.Sheafification.isLocallyInjective_toPlus_type (Scheme.smallEtaleTopology Z) P

/-- **Sheafification is locally injective on the small étale site.** Two sections of a presheaf
over an object of the small étale site of `Z` with the same image in the sheafification agree
after restriction along a covering family of that object. -/
public theorem equalizerSieve_mem_of_toSheafify_eq
    (P : Z.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) {W : Z.Etaleᵒᵖ} (x y : ToType (P.obj W))
    (h : (toSheafify (Scheme.smallEtaleTopology Z) P).app W x =
      (toSheafify (Scheme.smallEtaleTopology Z) P).app W y) :
    Presheaf.equalizerSieve x y ∈ Scheme.smallEtaleTopology Z W.unop := by
  set J := Scheme.smallEtaleTopology Z
  refine Presheaf.equalizerSieve_mem_of_equalizerSieve_app_mem J (J.toPlus P) x y ?_
  refine (isLocallyInjective_smallEtaleToPlus (J.plusObj P)).equalizerSieve_mem _ _ ?_
  have hfac := toSheafify_plusPlusIsoSheafify_hom J (Type (max (u + 1) v)) P
  have hinj : Function.Injective ((plusPlusIsoSheafify J (Type (max (u + 1) v)) P).hom.app W) :=
    ((isIso_iff_bijective _).mp inferInstance).1
  have e1 : ∀ c : ToType (P.obj W),
      (J.toSheafify P).app W c
        = (J.toPlus (J.plusObj P)).app W ((J.toPlus P).app W c) := by
    intro c
    rw [GrothendieckTopology.toSheafify, ← GrothendieckTopology.plusMap_toPlus]
    rfl
  have e2 : ∀ c : ToType (P.obj W),
      (plusPlusIsoSheafify J (Type (max (u + 1) v)) P).hom.app W
          ((J.toPlus (J.plusObj P)).app W ((J.toPlus P).app W c))
        = (toSheafify J P).app W c := by
    intro c
    rw [← e1 c, ← hfac]
    rfl
  apply hinj
  rw [e2 x, e2 y, h]

end Sheafify

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Equality in the left Kan extension is witnessed over a single object.** For a morphism
`k : V ⟶ W₀ ×_X Z` of the small étale site of `Z`, two sections of an étale sheaf over `W₀`
whose images under the unit of the left Kan extension agree after restriction along `k` already
agree over some object `W` of the small étale site of `X` admitting a morphism from `W₀` and a
morphism from `V` to `W ×_X Z`.

This is filteredness of the indexing category of the left Kan extension, which comes from
representable flatness of base change. -/
public theorem exists_globalSectionEqAt_of_lan_eq {V : Z.Etale} {W₀ : X.Etale}
    (k : V ⟶ (smallEtaleBaseChange i).obj W₀)
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    (a b : F.obj.obj (op W₀))
    (h : ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
          (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) a)
        = ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
          (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) b)) :
    ∃ (W : X.Etale) (q : W ⟶ W₀) (_ : V ⟶ (smallEtaleBaseChange i).obj W),
      F.obj.map q.op a = F.obj.map q.op b := by
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange i).op.lan.obj F.obj)
      ((smallEtaleBaseChange i).op.lanUnit.app F.obj) (op V)
  have hι : ∀ c : F.obj.obj (op W₀),
      ((Functor.LeftExtension.mk ((smallEtaleBaseChange i).op.lan.obj F.obj)
        ((smallEtaleBaseChange i).op.lanUnit.app F.obj)).coconeAt (op V)).ι.app
          (CostructuredArrow.mk k.op :
            CostructuredArrow (smallEtaleBaseChange i).op (op V)) c
        = ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
            (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) c) := fun _ ↦ rfl
  obtain ⟨jj, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (i := (CostructuredArrow.mk k.op :
      CostructuredArrow (smallEtaleBaseChange i).op (op V))) hcolim a b).mp
    (by rwa [hι a, hι b])
  exact ⟨jj.left.unop, φ.left.unop, jj.hom.unop, hφ⟩

variable (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- **Equality of presheaf-level pullbacks is local agreement over the image.** If two global
sections of a sheaf of sets on the small étale site of `X` have the same presheaf-level pullback
along `i : Z ⟶ X`, then for every point `z` of `Z` there is an object of the small étale site of
`X` whose image contains `i z` and over which the two sections agree. -/
public theorem exists_globalSectionEqAt_of_pullback_eq
    {a b : F.obj.obj (op (terminal X.Etale))}
    (hab : smallEtaleGlobalSectionPullback.{u, v} i g F a =
      smallEtaleGlobalSectionPullback.{u, v} i g F b)
    (z : Z) :
    ∃ W : X.Etale, GlobalSectionEqAt F a b W ∧ i.base z ∈ smallEtaleImage W := by
  set L := (smallEtaleBaseChange i).op.lan.obj F.obj
  set a' := L.map g.op
    (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale)) a)
  set b' := L.map g.op
    (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale)) b)
  have hR : Presheaf.equalizerSieve (F := L) a' b' ∈
      Scheme.smallEtaleTopology Z (terminal Z.Etale) :=
    equalizerSieve_mem_of_toSheafify_eq _ _ _ hab
  obtain ⟨α, Y, p, hEq⟩ := (Presheaf.equalizerSieve (F := L) a' b').exists_eq_ofArrows
  have hcov : ⋃ j, Set.range (p j).left = Set.univ :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp (hEq ▸ hR)
  obtain ⟨z₀, hz₀⟩ := surjective_terminal_hom Z z
  obtain ⟨j, v, hv⟩ : ∃ j, z₀ ∈ Set.range (p j).left :=
    Set.mem_iUnion.mp (hcov ▸ Set.mem_univ z₀)
  have hmem : L.map (p j).op a' = L.map (p j).op b' := by
    have hin : (Presheaf.equalizerSieve (F := L) a' b').arrows (p j) := by
      rw [hEq]
      exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, 𝟙 _, (Category.id_comp _).symm⟩
    exact hin
  have hmem' : L.map (p j ≫ g).op
        (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale)) a)
      = L.map (p j ≫ g).op
        (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale)) b) :=
    ((Functor.map_comp_apply _ g.op (p j).op _).trans hmem).trans
      (Functor.map_comp_apply _ g.op (p j).op _).symm
  obtain ⟨W, q, k, hq⟩ := exists_globalSectionEqAt_of_lan_eq i (p j ≫ g) F a b hmem'
  refine ⟨W, ?_, ?_⟩
  · rwa [Subsingleton.elim q (terminal.from W)] at hq
  · have hYj : ((Y j).hom : (Y j).left ⟶ Z).base v = z := by
      have hw : (p j).left ≫ ((terminal Z.Etale).hom : (terminal Z.Etale).left ⟶ Z) =
          ((Y j).hom : (Y j).left ⟶ Z) := MorphismProperty.Over.w (p j)
      calc ((Y j).hom : (Y j).left ⟶ Z).base v
          = ((p j).left ≫ ((terminal Z.Etale).hom :
              (terminal Z.Etale).left ⟶ Z)).base v := by rw [hw]
        _ = ((terminal Z.Etale).hom : (terminal Z.Etale).left ⟶ Z).base ((p j).left.base v) :=
              Scheme.Hom.comp_apply _ _ v
        _ = z := by rw [hv]; exact hz₀
    have hkw : k.left ≫ (((smallEtaleBaseChange i).obj W).hom :
        ((smallEtaleBaseChange i).obj W).left ⟶ Z) = ((Y j).hom : (Y j).left ⟶ Z) :=
      MorphismProperty.Over.w k
    have hsnd : (pullback.snd (W.hom : W.left ⟶ X) i).base (k.left.base v) = z :=
      Eq.trans ((Scheme.Hom.comp_apply k.left _ v).symm.trans
        (congrArg (fun f : (Y j).left ⟶ Z ↦ f.base v) hkw)) hYj
    refine ⟨(pullback.fst (W.hom : W.left ⟶ X) i).base (k.left.base v), ?_⟩
    have hcond : (pullback.fst (W.hom : W.left ⟶ X) i ≫ (W.hom : W.left ⟶ X)).base
          (k.left.base v)
        = (pullback.snd (W.hom : W.left ⟶ X) i ≫ i).base (k.left.base v) := by
      rw [pullback.condition]
    exact Eq.trans
      (((Scheme.Hom.comp_apply _ _ (k.left.base v)).symm.trans hcond).trans
        (Scheme.Hom.comp_apply _ _ (k.left.base v)))
      (congrArg i.base hsnd)

/-- **The injectivity half of Tag 09ZF, for the presheaf-level pullback.** Under hypothesis (1)
of the tag, the presheaf-level pullback of global sections along `i` is injective. -/
public theorem injective_smallEtaleGlobalSectionPullback_of_zariski
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G)) :
    Function.Injective (smallEtaleGlobalSectionPullback.{u, v} i g F) := fun _ _ hab ↦
  eq_of_forall_exists_globalSectionEqAt i hZar F
    (exists_globalSectionEqAt_of_pullback_eq i g F hab)

/-- **The injectivity half of Tag 09ZF, from hypothesis (1) alone.** If restriction of global
sections along `i : Z ⟶ X` is surjective for every sheaf of sets on the Zariski site of `X`, then
the comparison map on étale global sections is injective — no closed immersion, no
quasi-compactness and no hypothesis (2) needed. The whole of the tag is
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective`.
-/
public theorem injective_smallEtaleGlobalSectionsMapAt_of_zariskiSurjective
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G)) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v} i g F) :=
  injective_smallEtaleGlobalSectionsMapAt_of_zariski i g F hZar
    fun _ _ hab ↦ exists_globalSectionEqAt_of_pullback_eq i g F hab

end Stacks.EtaleCohomology

end

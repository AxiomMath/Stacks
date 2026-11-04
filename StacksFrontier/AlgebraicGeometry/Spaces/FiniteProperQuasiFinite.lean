module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedFieldBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringAffineCharts

/-!
# Finite morphisms of algebraic spaces are the proper morphisms with discrete fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Stacks 0A4X compares four
conditions on `f`: that it is finite; that it is proper and locally quasi-finite; that it is
proper and the point space of its fibre over every field-valued point of `Y` is discrete; and
that it is universally closed, separated, locally of finite type and has those discrete fibres.

All four conditions are compared here, and they are equivalent: properness is separatedness
together with being of finite type and universally closed, and the quasi-compactness half of
finite type comes for free from universal closedness by Stacks 04XW, so conditions (3) and (4)
differ by nothing; and local quasi-finiteness of a morphism locally of finite type is exactly
discreteness of all its field-valued fibres by Stacks 06RW. Condition (1) implies the other
three, by Stacks 04NZ and 04NY.

The remaining implication, that a proper locally quasi-finite morphism is finite, is proved one
point of `|Y|` at a time. Over a point `y` the fibre of `|X| → |Y|` is finite, because the fibre
of `f` over a field-valued point representing `y` is quasi-compact — `f` being universally
closed — as well as discrete, and surjects onto the set-theoretic fibre by Stacks 03H4. The
étale decomposition of Stacks 082H, applied to the finitely many points of that fibre, produces
an étale neighbourhood `(U, u)` of `y` and a decomposition `U ×_Y X = W ⊔ V` with `V` finite over
`U` and with no point of `|W|` over `u` mapping to a point of the fibre; as all points of the
fibre were used, no point of `|W|` lies over `u` at all. The morphism `W ⟶ U` is universally
closed, being a closed immersion followed by a base change of `f`, so the image of `|W|` in `|U|`
is closed and misses `u`, and `U` may be shrunk to the complementary open — again an object of
the site. Over the shrunken neighbourhood every point of the base change lies in `V` by part (1)
of Stacks 03BZ, so the base change factors through `V` by Stacks 03IE and is a base change of the
finite `V ⟶ U`. Replacing each neighbourhood by the open subspace of `Y` it sweeps out, which
receives a surjective étale chart from it by Stacks 06NF, Stacks 03ZQ descends finiteness to
those open subspaces and then assembles it from the Zariski covering they form.

The fibre over a field-valued point is the pullback of `f` along the morphism out of the field
spectrum presented by that point, taken in the order Stacks 06RW uses, so that discreteness is
literally the condition appearing there.

Stacks 0A4Y localizes the implication (2) ⇒ (1) on the base: a proper morphism which is
quasi-finite only at the points above a single point `y` of `|Y|` is finite over some open
neighbourhood of `y`. The locus where `f` is quasi-finite is open by Stacks 04NW, so its
complement is closed, and universal closedness makes the image of that complement closed and
— by the hypothesis at `y` — disjoint from `y`. The open subspace of `Y` cut out by the
complement of that image, which exists by part (1) of Stacks 03BZ, is the neighbourhood: the
base change of `f` over it is proper, and locally quasi-finite because quasi-finiteness at a
point passes between a morphism and its base change by part (2) of Stacks 0ABM.

## Main results

* `AlgebraicGeometry.Space.isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres`:
  **Stacks 0A4X**, conditions (2) and (3).
* `AlgebraicGeometry.Space.isProper_iff_universallyClosed_isSeparated_isLocallyOfFiniteType`:
  **Stacks 0A4X**, conditions (3) and (4). The discreteness clause is common to the two
  conditions, so comparing them is comparing properness with the remaining three conditions,
  and that comparison holds for every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isFinite_of_isProper_of_isLocallyQuasiFinite`: **Stacks 0A4X**,
  condition (2) implies condition (1), hence conditions (3) and (4) do too.
* `AlgebraicGeometry.Space.isProper_and_isLocallyQuasiFinite_of_isFinite`: **Stacks 0A4X**,
  condition (1) implies condition (2), hence also conditions (3) and (4).
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_isProper`:
  **Stacks 0A4Y**, finiteness over an open neighbourhood of a point above which the morphism
  is quasi-finite.
* `AlgebraicGeometry.Space.finite_setFibre_of_universallyClosed_of_discrete_fibre`: the
  set-theoretic fibre of a universally closed morphism over a point of `|Y|` whose field fibre
  has discrete point space is finite.

## References

* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 04NY](https://stacks.math.columbia.edu/tag/04NY)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Restricting a cartesian square along a monomorphism -/

/-- **Restricting a cartesian square along a monomorphism into its top right corner.** If the
top edge `fst` of a cartesian square factors as `k ≫ m` through a monomorphism `m`, then the
square obtained by replacing that edge with `k` and the right edge `f` with `m ≫ f` is again
cartesian.

A cone over the restricted cospan is a cone over the original one, by composing its first leg
with `m`, so it receives a lift; the lift factors through `k` because `m` is a monomorphism, and
it is unique because it is unique for the original square. -/
private theorem isPullback_of_comp_mono_left {C : Type*} [Category C] {P X Y Z V : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    {m : V ⟶ X} [Mono m] {k : P ⟶ V} (hk : k ≫ m = fst) :
    IsPullback k snd (m ≫ f) g := by
  have hw : k ≫ m ≫ f = snd ≫ g := by rw [← Category.assoc, hk, h.w]
  have hcond : ∀ s : PullbackCone (m ≫ f) g, (s.fst ≫ m) ≫ f = s.snd ≫ g := fun s ↦
    (Category.assoc _ _ _).trans s.condition
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s ↦ h.lift (s.fst ≫ m) s.snd (hcond s)) (fun s ↦ ?_) (fun s ↦ h.lift_snd _ _ _)
    (fun s n h₁ h₂ ↦ ?_))
  · exact (cancel_mono m).1 (by rw [Category.assoc, hk, h.lift_fst])
  · have e : n ≫ fst = s.fst ≫ m := by rw [← hk, ← Category.assoc, h₁]
    exact h.hom_ext (e.trans (h.lift_fst _ _ (hcond s)).symm)
      (h₂.trans (h.lift_snd _ _ (hcond s)).symm)

/-- **Base change along a composite is an iterated base change.** For `h : V ⟶ U`,
`g : U ⟶ Y` and `f : X ⟶ Y`, the projection `pullback (h ≫ g) f ⟶ V` is the base change of
`pullback.fst g f` along `h`. -/
private theorem isPullback_pullbackRightPullbackFstIso_inv {C : Type*} [Category C]
    [HasPullbacks C] {U V X Y : C} (g : U ⟶ Y) (f : X ⟶ Y) (h : V ⟶ U) :
    IsPullback ((pullbackRightPullbackFstIso g f h).inv ≫ pullback.snd h (pullback.fst g f))
      (pullback.fst (h ≫ g) f) (pullback.fst g f) h := by
  refine ((IsPullback.of_hasPullback h (pullback.fst g f)).flip).of_iso'
    (pullbackRightPullbackFstIso g f h).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

/-! ### The point set of a locally covering pair of open subspaces -/

/-- **Two open subspaces whose join sheafifies to everything cover the point space.** The
subspace cut out by the union of the two point sets contains both pieces, hence their join, and
it is an fppf sheaf, so it contains the sheafification of that join — all of `P`. Its point set
is therefore the whole point space, and that point set is the union by part (1) of Stacks
03BZ. -/
private theorem union_range_pointsMap_ι_of_sheafify_sup_eq_top
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (W V : Subfunctor P)
    (hsup : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤) :
    Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ := by
  set T : Set (points B S hS P) :=
    Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι)
  have hWle : W ≤ openSubspaceOfPoints B S hS P T := by
    rw [← Subfunctor.range_ι W]
    exact (range_le_openSubspaceOfPoints_range_pointsMap W.ι).trans
      (openSubspaceOfPoints_mono B S hS Set.subset_union_left)
  have hVle : V ≤ openSubspaceOfPoints B S hS P T := by
    rw [← Subfunctor.range_ι V]
    exact (range_le_openSubspaceOfPoints_range_pointsMap V.ι).trans
      (openSubspaceOfPoints_mono B S hS Set.subset_union_right)
  have hle : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) ≤
      openSubspaceOfPoints B S hS P T :=
    Subfunctor.sheafify_le _ _ (sup_le hWle hVle) ((isSheaf_iff_isSheaf_of_type _ _).1 hP.isSheaf)
      ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_openSubspaceOfPoints B S hS hP.isSheaf T))
  have hTtop : openSubspaceOfPoints B S hS P T = ⊤ :=
    le_antisymm le_top (by rwa [← hsup])
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := P) T
  rw [hTtop] at hrange
  exact hrange.symm.trans
    (Set.range_eq_univ.2
      (bijective_pointsMap_of_isIso B S hS (Subfunctor.ι (⊤ : Subfunctor P))).2)

/-! ### Finiteness of the fibres of a universally closed morphism -/

/-- **A universally closed morphism with a discrete field fibre has a finite fibre.** For a
field-valued point `p` of the target, with `y` the point of `|Y|` it represents, the fibre of
`f` over the field spectrum of `p` has compact point space, being universally closed over a
one-point base; if its point space is moreover discrete then it is finite, and so is the
set-theoretic fibre `f^{-1}({y}) ⊂ |X|`, onto which it surjects by Stacks 03H4. -/
theorem finite_setFibre_of_universallyClosed_of_discrete_fibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (huc : UniversallyClosed B S hS f) (p : FieldValuedPoint B S hS Y)
    (hd : DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f))) :
    (setFibre B S hS f p).Finite := by
  have hcpt : CompactSpace (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
    compactSpace_points_of_universallyClosed_of_subsingleton_base B S hS
      (p.siteObject B S hS Y) p.carrier p.contained (𝟙 _)
      (subsingleton_points_yoneda_siteObject B S hS p)
      (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
        (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY)
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y))
      (pullback.fst (yonedaEquiv.symm p.value) f)
      (universallyClosed_pullback B S hS f (yonedaEquiv.symm p.value) huc)
  have : Finite (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
    @finite_of_compact_of_discrete _ _ hcpt hd
  have hfin : Finite (points B S hS (fieldFibre B S hS f p)) :=
    Finite.of_injective _
      (bijective_pointsMap_of_isIso B S hS
        (pullbackSymmetry f (yonedaEquiv.symm p.value)).hom).1
  exact finite_setFibre_of_finite_fieldFibre B S hS hX hY f p (Set.finite_univ_iff.mpr hfin)

/-! ### Conditions (2) and (3) -/

/-- **Stacks 0A4X, conditions (2) and (3).** A proper morphism of algebraic spaces over `S` is
locally quasi-finite exactly when the point space of its fibre over every field-valued point of
its target is discrete.

A proper morphism is locally of finite type, and for a morphism locally of finite type the two
conditions are compared by Stacks 06RW. -/
@[stacks 0A4X "conditions (2) and (3)"]
theorem isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (IsProper B S hS f ∧ IsLocallyQuasiFinite B S hS f) ↔
      (IsProper B S hS f ∧ ∀ p : FieldValuedPoint B S hS Y,
        DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f))) :=
  and_congr_right fun hp ↦
    isLocallyQuasiFinite_iff_forall_discreteTopology_fibre B S hS hX hY f hp.2.1.1

/-! ### Conditions (3) and (4) -/

/-- **Stacks 0A4X, conditions (3) and (4).** A morphism of algebraic spaces over `S` is proper
exactly when it is universally closed, separated and locally of finite type.

Properness of Stacks 03ZM is separatedness together with being of finite type and universally
closed, and being of finite type is being locally of finite type together with quasi-compactness;
quasi-compactness is implied by universal closedness alone, by Stacks 04XW, so it is not an extra
condition. Conditions (3) and (4) of Stacks 0A4X share their discreteness clause and differ only
by this comparison. -/
@[stacks 0A4X "conditions (3) and (4)"]
theorem isProper_iff_universallyClosed_isSeparated_isLocallyOfFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsProper B S hS f ↔
      UniversallyClosed B S hS f ∧ IsSeparated B S hS f ∧ IsLocallyOfFiniteType B S hS f :=
  ⟨fun hp ↦ ⟨hp.2.2, hp.1, hp.2.1.1⟩, fun ⟨huc, hsep, hlft⟩ ↦
    ⟨hsep, ⟨hlft, isQuasiCompact_of_universallyClosed B S hS hX hY f huc⟩, huc⟩⟩

/-! ### Condition (2) implies condition (1) -/

/-- **An étale neighbourhood of a point over which a proper locally quasi-finite morphism
becomes finite.** This is the body of the implication (4) ⇒ (1) of Stacks 0A4X, carried out at
one point `y` of `|Y|`.

Represent `y` by a field-valued point `p`. The morphism is universally closed, so its fibre over
`p` has finite point space and the set-theoretic fibre `f^{-1}(\{y\})` is finite; enumerate it as
`x₁, …, x_n`. The morphism is quasi-finite at each `xᵢ`, being locally quasi-finite, so Stacks
082H supplies an étale `g : h_U ⟶ Y` hitting `y`, together with a decomposition of `U ×_Y X` into
two open-and-closed subspaces `W` and `V` with `V` finite over `U` and with no point of `|W|`
over the chosen point `u` of `|U|` lying over any `xᵢ`. Since the fibre of `|X| → |Y|` over `y`
is exactly `\{x₁, …, x_n\}`, no point of `|W|` lies over `u` at all. The morphism
`W ⟶ U` is universally closed — a closed immersion followed by a base change of `f` — so the
image of `|W|` in `|U|` is closed and misses `u`; restricting `U` to the complementary open,
which is again an object of the site, every point of the restricted base change lies in `V` by
Stacks 03BZ, hence the restricted base change factors through `V` by Stacks 03IE, and that
factorization exhibits it as a base change of the finite `V ⟶ U`. -/
private theorem exists_etale_isFinite_pullback_snd_of_isProper
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) (hqf : IsLocallyQuasiFinite B S hS f) (y : points B S hS Y) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y),
      IsEtale B S hS g ∧ y ∈ Set.range (pointsMap B S hS (yoneda.obj U) g) ∧
      IsFinite B S hS (pullback.snd f g) := by
  classical
  have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  have huc : UniversallyClosed B S hS f := hp.2.2
  have hdisc := ((isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres
    B S hS hX hY f).mp ⟨hp, hqf⟩).2
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  -- the set-theoretic fibre over `y` is finite; enumerate it
  have _ : Finite (setFibre B S hS f p) :=
    (finite_setFibre_of_universallyClosed_of_discrete_fibre B S hS hX hY f huc p
      (hdisc p)).to_subtype
  obtain ⟨n, ⟨enum⟩⟩ := Finite.exists_equiv_fin (setFibre B S hS f p)
  have hx : ∀ i : Fin n,
      pointsMap B S hS X f ((enum.symm i : points B S hS X)) = p.class B S hS Y :=
    fun i ↦ (enum.symm i).2
  have hxall : ∀ z : points B S hS X, pointsMap B S hS X f z = p.class B S hS Y →
      ∃ i : Fin n, z = ((enum.symm i : points B S hS X)) := fun z hz ↦
    ⟨enum ⟨z, hz⟩, by rw [Equiv.symm_apply_apply]⟩
  -- the étale decomposition of Stacks 082H
  obtain ⟨U, g, u, W, V, hgE, hgu, -, hWc, hVo, -, hsup, -, hVfin, -, hWpt⟩ :=
    exists_etale_decomposition_isFinite_of_isQuasiFiniteAt B S hS hX hY f (p.class B S hS Y)
      (fun i : Fin n ↦ ((enum.symm i : points B S hS X))) hx hp.2.1.1 hp.1
      (fun i ↦ isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hX hqf _) (Or.inl hp.2.1.2)
  have hPalg : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS U) hX hY
  -- no point of `|W|` lies over `u`
  have hWu : ∀ t : points B S hS W.toFunctor,
      pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f) t ≠ u := by
    intro t ht
    have hcomm : (W.ι ≫ pullback.fst g f) ≫ g = (W.ι ≫ pullback.snd g f) ≫ f := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have h1 : pointsMap B S hS X f
        (pointsMap B S hS W.toFunctor (W.ι ≫ pullback.snd g f) t) = p.class B S hS Y := by
      rwa [← pointsMap_apply_comm B S hS hcomm t, ht]
    obtain ⟨i, hi⟩ := hxall _ h1
    exact hWpt t ht i hi
  -- the image of `|W|` in `|U|` is closed and misses `u`
  have hucW : UniversallyClosed B S hS (W.ι ≫ pullback.fst g f) :=
    universallyClosed_comp B S hS hPalg (isAlgebraicSpace_yoneda B S hS U) W.ι
      (pullback.fst g f)
      (universallyClosed_of_isClosedImmersion B S hS hWc.1 hPalg W.ι hWc.2)
      (universallyClosed_pullback B S hS f g huc)
  have hclosed : IsClosed
      (Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f))) := by
    exact (isClosed_of_universallyClosed B S hS (isAlgebraicSpace_yoneda B S hS U)
      (W.ι ≫ pullback.fst g f) hucW).isClosed_range
  have hΩopen : IsOpen ((pointsToScheme B S hS U ''
      Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f)))ᶜ) :=
    ((isClosed_pointTopology_yoneda_iff_isClosed_image B S hS U _).1 hclosed).isOpen_compl
  have huΩ : pointsToScheme B S hS U u ∈ (pointsToScheme B S hS U ''
      Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f)))ᶜ := by
    rintro ⟨c, ⟨t, ht⟩, hceq⟩
    exact hWu t (ht.trans (injective_pointsToScheme B S hS U hceq))
  -- shrink `U` to that complement
  obtain ⟨U', j, hjoi, hjrange, -⟩ := exists_restrict_bigFppfOver U ⟨_, hΩopen⟩
  have hjE : IsEtale B S hS (yoneda.map j) :=
    isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) j).2 hjoi))
  have hu' : u ∈ Set.range (pointsMap B S hS (yoneda.obj U') (yoneda.map j)) :=
    mem_range_pointsMap_yoneda_map B S hS j u (by rwa [hjrange])
  -- the restricted base change, compared with the base change of `pullback.fst g f`
  have hsq : IsPullback
      ((pullbackRightPullbackFstIso g f (yoneda.map j)).inv ≫
        pullback.snd (yoneda.map j) (pullback.fst g f))
      (pullback.fst (yoneda.map j ≫ g) f) (pullback.fst g f) (yoneda.map j) :=
    isPullback_pullbackRightPullbackFstIso_inv g f (yoneda.map j)
  -- every point of the restricted base change lies in `V`
  have hcov := union_range_pointsMap_ι_of_sheafify_sup_eq_top B S hS hPalg W V hsup
  have hrange : Set.range (pointsMap B S hS (pullback (yoneda.map j ≫ g) f)
      ((pullbackRightPullbackFstIso g f (yoneda.map j)).inv ≫
        pullback.snd (yoneda.map j) (pullback.fst g f))) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
    rintro _ ⟨q, rfl⟩
    rcases hcov.ge (Set.mem_univ (pointsMap B S hS (pullback (yoneda.map j ≫ g) f)
      ((pullbackRightPullbackFstIso g f (yoneda.map j)).inv ≫
        pullback.snd (yoneda.map j) (pullback.fst g f)) q)) with ⟨t, ht⟩ | hv
    · exfalso
      have heq : pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f) t =
          pointsMap B S hS (yoneda.obj U') (yoneda.map j)
            (pointsMap B S hS (pullback (yoneda.map j ≫ g) f)
              (pullback.fst (yoneda.map j ≫ g) f) q) := by
        rw [pointsMap_comp_apply, ht]
        exact pointsMap_apply_comm B S hS hsq.w q
      have hnot : pointsToScheme B S hS U
          (pointsMap B S hS (yoneda.obj U') (yoneda.map j)
            (pointsMap B S hS (pullback (yoneda.map j ≫ g) f)
              (pullback.fst (yoneda.map j ≫ g) f) q)) ∉
          pointsToScheme B S hS U ''
            Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f)) := by
        rw [pointsToScheme_pointsMap_yoneda]
        have hr : (BigFppfOver.toScheme B S hS).map j
            (pointsToScheme B S hS U' (pointsMap B S hS
              (pullback (yoneda.map j ≫ g) f) (pullback.fst (yoneda.map j ≫ g) f) q)) ∈
            Set.range ((BigFppfOver.toScheme B S hS).map j) := ⟨_, rfl⟩
        rwa [hjrange] at hr
      exact hnot (heq ▸ Set.mem_image_of_mem _ ⟨t, rfl⟩)
    · exact hv
  obtain ⟨kk, hkk⟩ := (factorsThrough_openSubspace_iff_points B S hS hPalg
    (isAlgebraicSpace_pullback B S hS (yoneda.map j ≫ g) f
      (isAlgebraicSpace_yoneda B S hS U') hX hY) _ hVo _).2 hrange
  have hfinfst : IsFinite B S hS (pullback.fst (yoneda.map j ≫ g) f) :=
    isFinite_of_isPullback B S hS (isPullback_of_comp_mono_left hsq hkk) hVfin
  refine ⟨U', yoneda.map j ≫ g, isEtale_comp B S hS hjE hgE, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hu'
    exact ⟨w, by rwa [pointsMap_comp_apply, hw]⟩
  · have h := isFinite_isIso_comp (pullbackSymmetry f (yoneda.map j ≫ g)).hom hfinfst
    rwa [pullbackSymmetry_hom_comp_fst] at h

/-- **Stacks 0A4X, condition (2) implies condition (1).** A proper, locally quasi-finite
morphism of algebraic spaces over `S` is finite.

Every point of `|Y|` has an étale neighbourhood over which `f` becomes finite,
by `AlgebraicGeometry.Space.exists_etale_isFinite_pullback_snd_of_isProper`. Replacing such a
neighbourhood by the open subspace of `Y` it sweeps out, which receives a surjective étale chart
from it by Stacks 06NF, finiteness descends along that chart by Stacks 03ZQ; the resulting open
subspaces cover `|Y|`, indexed by the points of the underlying scheme of an étale atlas of `Y` so
that the index type has the right size, and finiteness is Zariski-local on the target, again by
Stacks 03ZQ. -/
@[stacks 0A4X "condition (2) implies condition (1)",
  ega "III 4.4.11" "proper q-finite ⇒ finite",
  ega "IV 18.12.4" "proper q-finite⇒finite", ega "III 4.4.2" "c) => a)"]
theorem isFinite_of_isProper_of_isLocallyQuasiFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) (hqf : IsLocallyQuasiFinite B S hS f) :
    IsFinite B S hS f := by
  classical
  have key : ∀ y : points B S hS Y, ∃ Y' : Subfunctor Y, IsOpenSubspace B S hS Y' ∧
      y ∈ Set.range (pointsMap B S hS Y'.toFunctor Y'.ι) ∧
      IsFinite B S hS (pullback.snd f Y'.ι) := by
    intro y
    obtain ⟨U, g, hgE, hgy, hgfin⟩ :=
      exists_etale_isFinite_pullback_snd_of_isProper B S hS hX hY f hp hqf y
    obtain ⟨hopen, hψe, hψsurj, -⟩ :=
      isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda B S hS hY U g
        (presheaf_etale_of_isEtale B S hS hgE)
    refine ⟨openSubspaceOfPoints B S hS Y (Set.range (pointsMap B S hS (yoneda.obj U) g)),
      hopen, by rwa [range_pointsMap_ι_openSubspaceOfPoints], ?_⟩
    set Y' := openSubspaceOfPoints B S hS Y (Set.range (pointsMap B S hS (yoneda.obj U) g))
    set ψ := Subfunctor.lift g (range_le_openSubspaceOfPoints_range_pointsMap g) with hψdef
    have hpaste : IsPullback
        (pullback.fst (pullback.snd f Y'.ι) ψ ≫ pullback.fst f Y'.ι)
        (pullback.snd (pullback.snd f Y'.ι) ψ) f (ψ ≫ Y'.ι) :=
      (IsPullback.of_hasPullback (pullback.snd f Y'.ι) ψ).paste_horiz
        (IsPullback.of_hasPullback f Y'.ι)
    rw [hψdef, Subfunctor.lift_ι] at hpaste
    refine isFinite_of_surjectiveEtaleChart B S hS
      (isAlgebraicSpace_pullback B S hS f Y'.ι hX hopen.1 hY) hopen.1
      (pullback.snd f Y'.ι) hψsurj (isEtale_of_presheaf_etale B S hS hψe) ?_
    have h := isFinite_isIso_comp
      (hpaste.isoIsPullback _ _ (IsPullback.of_hasPullback f g)).hom hgfin
    rwa [IsPullback.isoIsPullback_hom_snd] at h
  choose Ysub hYopen hYmem hYfin using key
  obtain ⟨A, qA, hqs, -⟩ := hY.exists_atlas
  refine (isFinite_iff_zariskiCover B S hS f hX hY).2
    ⟨(BigFppfOver.toScheme B S hS).obj A,
      fun a ↦ Ysub (pointsMap B S hS (yoneda.obj A) qA ((pointsEquivScheme B S hS A).symm a)),
      ?_, fun a ↦ hYfin _⟩
  refine (isZariskiCover_iff_iUnion_points B S hS Y hY _ _ fun a ↦ hYopen _).2
    (Set.eq_univ_of_forall fun z ↦ ?_)
  obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY A qA).1 hqs z
  refine Set.mem_iUnion.2 ⟨pointsEquivScheme B S hS A w, ?_⟩
  rw [Equiv.symm_apply_apply, hw]
  exact hYmem z

/-! ### Condition (1) implies the others -/

/-- **Stacks 0A4X, condition (1) implies condition (2).** A finite morphism of algebraic spaces
over `S` is proper and locally quasi-finite.

Properness is the second half of the characterization of finiteness as affineness together with
properness, Stacks 04NZ, and local quasi-finiteness is the first half of quasi-finiteness of a
finite morphism, Stacks 04NY. -/
@[stacks 0A4X "condition (1) implies condition (2)"]
theorem isProper_and_isLocallyQuasiFinite_of_isFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFinite B S hS f) :
    IsProper B S hS f ∧ IsLocallyQuasiFinite B S hS f :=
  ⟨((isFinite_iff_isAffineHom_and_isProper B S hS hX hY f).mp hf).2,
    (isQuasiFinite_of_isFinite B S hS f hX hY hf).1⟩

/-- **Stacks 0A4X, condition (1) implies condition (3).** A finite morphism of algebraic spaces
over `S` is proper and the point space of its fibre over every field-valued point of its target
is discrete. -/
@[stacks 0A4X "condition (1) implies condition (3)",
  ega "IV 18.12.4" "finite⇒proper+discrete",
  ega "II 6.1.7" "discrete fibres", ega "III 4.4.2" "a) => c)"]
theorem isProper_and_discreteFibres_of_isFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFinite B S hS f) :
    IsProper B S hS f ∧ ∀ p : FieldValuedPoint B S hS Y,
      DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
  (isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres B S hS hX hY f).mp
    (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hX hY f hf)

/-- **Stacks 0A4X, condition (1) implies condition (4).** A finite morphism of algebraic spaces
over `S` is universally closed, separated and locally of finite type, and the point space of its
fibre over every field-valued point of its target is discrete. -/
@[stacks 0A4X "condition (1) implies condition (4)"]
theorem universallyClosed_isSeparated_isLocallyOfFiniteType_and_discreteFibres_of_isFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFinite B S hS f) :
    UniversallyClosed B S hS f ∧ IsSeparated B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
      ∀ p : FieldValuedPoint B S hS Y,
        DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)) := by
  obtain ⟨hp, hdisc⟩ := isProper_and_discreteFibres_of_isFinite B S hS hX hY f hf
  obtain ⟨huc, hsep, hlft⟩ :=
    (isProper_iff_universallyClosed_isSeparated_isLocallyOfFiniteType B S hS hX hY f).mp hp
  exact ⟨huc, hsep, hlft, hdisc⟩

/-! ### Finiteness over an open neighbourhood of a point of the target -/

/-- **Stacks 0A4Y.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` and let
`y` be a point of `|Y|` such that `f` is quasi-finite at every point of `|X|` lying over `y`.
Then `y` has an open neighbourhood `V ⊆ Y` over which `f` becomes finite, in the sense that the
base change `f^{-1}(V) ⟶ V` is finite.

The locus in `|X|` where `f` is quasi-finite is open — that is Stacks 04NW, in the point-set
form of part (1) of Stacks 0ABM — so its
complement `Z` is closed; `f` is universally closed, hence closed, so the image of `Z` is closed
in `|Y|`, and the hypothesis at `y` says exactly that `y` is not in that image. Take for `V` the
open subspace of `Y` with point set the complement of the image of `Z`, which exists by part (1)
of Stacks 03BZ. The base change `f^{-1}(V) ⟶ V` is proper, and it is locally quasi-finite
because each of its points maps to a point of `|X|` whose image in `|Y|` avoids the image of
`Z`, hence lies outside `Z`, and quasi-finiteness at a point transfers to a base change by part
(2) of Stacks 0ABM. It is therefore finite by Stacks 0A4X. -/
@[stacks 0A4Y]
theorem exists_isOpenSubspace_isFinite_pullback_snd_of_isProper
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) (y : points B S hS Y)
    (hqf : ∀ x : points B S hS X, pointsMap B S hS X f x = y → IsQuasiFiniteAt B S hS f x) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  have hft : IsFiniteType B S hS f := hp.2.1
  -- the quasi-finite locus is open, so the image of its complement is closed and misses `y`
  have himg := isClosed_of_universallyClosed B S hS hY f hp.2.2 _
    (isOpen_setOf_isQuasiFiniteAt B S hS f).isClosed_compl
  set T := pointsMap B S hS X f '' {x : points B S hS X | IsQuasiFiniteAt B S hS f x}ᶜ
  have hynot : y ∉ T := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hqf x rfl)
  -- the open subspace of `Y` cut out by the complement of that image
  set V := openSubspaceOfPoints B S hS Y Tᶜ
  have hVopen : IsOpenSubspace B S hS V :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ himg.isOpen_compl
  have hVa : IsAlgebraicSpace B S hS V.toFunctor := hVopen.1
  have hVrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ
  have hP : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hX hVa hY
  have hsq : IsPullback (pullback.snd f V.ι) (pullback.fst f V.ι) V.ι f :=
    (IsPullback.of_hasPullback f V.ι).flip
  -- the base change is proper
  have hproper : IsProper B S hS (pullback.snd f V.ι) :=
    ⟨isSeparated_pullbackSnd B S hS V.ι hp.1,
      IsFiniteType.of_isPullback B S hS hsq hX hY hft,
      universallyClosed_of_isPullback B S hS hP hX hVa hY f V.ι hp.2.2 hsq⟩
  -- and locally quasi-finite, one point at a time
  have hlqf : IsLocallyQuasiFinite B S hS (pullback.snd f V.ι) := by
    refine (isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hP hVa _).2 fun w ↦ ?_
    refine (isQuasiFiniteAt_iff_of_isPullback B S hS hsq hX hY hVa hft.1 w).2 ?_
    by_contra hcon
    have hnot : pointsMap B S hS V.toFunctor V.ι
        (pointsMap B S hS (pullback f V.ι) (pullback.snd f V.ι) w) ∈ Tᶜ := by
      rw [← hVrange]
      exact Set.mem_range_self _
    exact hnot ⟨_, hcon, pointsMap_apply_comm B S hS pullback.condition w⟩
  exact ⟨V, hVopen, by rwa [hVrange],
    isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hP hVa _ hproper hlqf⟩

end AlgebraicGeometry.Space

end

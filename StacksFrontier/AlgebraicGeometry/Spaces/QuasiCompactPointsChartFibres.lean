module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions

/-!
# Finiteness of the chart fibres above a point of an algebraic space

Stacks 03JS compares two conditions on a point `x` of an algebraic space `X` over a scheme `S`:
that *some* family of étale charts `U_i ⟶ X` whose disjoint union is surjective has finite
fibres of `|U_i| → |X|` above `x`, and that *every* étale chart with affine source has finite
fibre of `|U| → |X|` above `x`. This file proves both implications.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.finite_inter_preimage_singleton_of_etale`: an étale morphism of schemes
  has finite fibres above every point after intersecting with an affine open of the source
  which the morphism carries into an affine open of the target. This is the scheme-level input.
* `AlgebraicGeometry.Space.exists_pointsMap_eq_of_isSurjective_sigmaDesc`: a family of
  morphisms of presheaves whose coproduct is surjective on the points of Tag 03BU is jointly
  surjective on those points.
* `AlgebraicGeometry.Space.finite_chartFibre_of_jointlySurjective` is the substance of
  Stacks 03JS: a jointly surjective family of étale charts with finite chart fibres above `x`
  forces every étale chart with *quasi-compact* source to have a finite chart fibre above `x`.
* `AlgebraicGeometry.Space.finite_chartFibre_of_etaleCover` is Stacks 03JS, part (1) implies
  part (2), and `AlgebraicGeometry.Space.exists_etaleCover_finite_chartFibre` is part (2)
  implies part (1).

## Implementation notes

The argument is the source's. Write `W_i = h_U ×_X h_{U_i}`, which is representable because the
chart `φ : h_U ⟶ X` is étale, with projections `q_i : W_i ⟶ U` and `p_i : W_i ⟶ U_i`; both are
étale on underlying schemes, `q_i` because `φ_i` is étale and `p_i` because `φ` is. So `q_i` is
open on the points of Tag 03BX by clause (3) of that tag, and the `q_i` are jointly surjective
on points by Tag 03H4. Every point of `|U|` therefore lies in the image of an affine open of
some `W_i`, chosen small enough that `p_i` carries it into an affine open of `U_i`, and these
images form an open cover of `|U|`, which is quasi-compact. Finitely many of them suffice. On
each of those affine opens `p_i` is an étale morphism between affine schemes, hence quasi-compact
and locally quasi-finite, so Stacks 0AAY makes its fibres finite; the chart fibre above `x` is
contained in the union over the finitely many chosen opens of the `q_i`-image of the part lying
over the — finite — chart fibre of `φ_i` above `x`.

Two deliberate departures from the source. First, the source invokes Stacks 03JA, that a locally
quasi-finite morphism with quasi-compact source has universally bounded fibres, to see that the
fibres of `p_i` restricted to a quasi-compact open are finite. That route is available
(`AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite`) but passing from a bound
on the fibre degrees to finiteness of the underlying sets goes through a private lemma; the open
is therefore shrunk until `p_i` restricted to it is a morphism of *affine* schemes, which is
quasi-compact outright, and then Stacks 0AAY applies directly. Second, the family of
condition (1) is only used through joint surjectivity on points, so the substance is proved for
an arbitrary index type with that hypothesis, and the tagged statement — where the index type is
forced to `Type u` by the presheaf coproduct, exactly as recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPointsConditions.lean` — is a corollary.

The source asks in part (2) for an *affine* chart; the proof needs only that the chart has
quasi-compact underlying scheme, and
`AlgebraicGeometry.Space.finite_chartFibre_of_jointlySurjective` is stated that way. The tagged
corollary keeps the source's affineness hypothesis.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 0AAY](https://stacks.math.columbia.edu/tag/0AAY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An étale morphism of schemes has finite fibres on an affine open of its source which it
carries into an affine open of its target.

The restricted morphism is étale between affine schemes, hence quasi-compact and locally
quasi-finite, so Stacks 0AAY applies: the quasi-finite points of one of its fibres are finite in
number, and étaleness makes every point quasi-finite. -/
theorem finite_inter_preimage_singleton_of_etale {T V : Scheme.{u}} (f : T ⟶ V) [Etale f]
    {A : T.Opens} (hA : IsAffineOpen A) {V' : V.Opens} (hV' : IsAffineOpen V')
    (hle : A ≤ f ⁻¹ᵁ V') (v : V) :
    (f ⁻¹' {v} ∩ (A : Set T)).Finite := by
  have hAaff : IsAffine (A : Scheme.{u}) := hA
  have hV'aff : IsAffine (V' : Scheme.{u}) := hV'
  set g : (A : Scheme.{u}) ⟶ (V' : Scheme.{u}) := T.homOfLE hle ≫ (f ∣_ V') with hg
  have hgι : g ≫ V'.ι = A.ι ≫ f := by
    rw [hg, Category.assoc, morphismRestrict_ι, ← Category.assoc, T.homOfLE_ι]
  have hgpt : ∀ a : (A : Scheme.{u}), V'.ι (g a) = f (A.ι a) :=
    fun a => congrFun (congrArg (fun k : (A : Scheme.{u}) ⟶ V => (k : _ → _)) hgι) a
  obtain ⟨hft, hlqf⟩ := locallyQuasiFinite_of_etale g
  by_cases hv : v ∈ V'
  · have hfin := finite_setOf_mapsTo_and_quasiFiniteAt g ⟨v, hv⟩
    have heq : {a : (A : Scheme.{u}) | g a = ⟨v, hv⟩ ∧ quasiFiniteAt g a} =
        {a : (A : Scheme.{u}) | g a = ⟨v, hv⟩} := by
      ext a
      simp only [Set.mem_ofPred_eq,
        and_iff_left ((forall_quasiFiniteAt_iff g).mpr ⟨hft, hlqf⟩ a)]
    rw [heq] at hfin
    have himg : A.ι '' {a : (A : Scheme.{u}) | g a = ⟨v, hv⟩} = f ⁻¹' {v} ∩ (A : Set T) := by
      ext t
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨?_, a.2⟩
        change f (A.ι a) = v
        rw [← hgpt a, show g a = ⟨v, hv⟩ from ha]
        rfl
      · rintro ⟨ht, htA⟩
        replace ht : f t = v := ht
        exact ⟨⟨t, htA⟩, Subtype.ext ((hgpt ⟨t, htA⟩).trans ht), rfl⟩
    rw [← himg]
    exact hfin.image _
  · exact Set.finite_empty.subset fun t ht => hv ((show f t = v from ht.1) ▸ hle ht.2)

/-- An étale morphism of schemes has finite preimage of a finite set on an affine open of its
source which it carries into an affine open of its target. -/
theorem finite_inter_preimage_of_etale {T V : Scheme.{u}} (f : T ⟶ V) [Etale f]
    {A : T.Opens} (hA : IsAffineOpen A) {V' : V.Opens} (hV' : IsAffineOpen V')
    (hle : A ≤ f ⁻¹ᵁ V') {E : Set V} (hE : E.Finite) :
    (f ⁻¹' E ∩ (A : Set T)).Finite :=
  (hE.biUnion fun v _ => finite_inter_preimage_singleton_of_etale f hA hV' hle v).subset
    fun t ht => Set.mem_biUnion (x := f t) ht.1 ⟨Set.mem_singleton _, ht.2⟩

/-- Every point of the source of a morphism of schemes lies in an affine open which the morphism
carries into an affine open of its target. -/
theorem exists_isAffineOpen_le_preimage {X Y : Scheme.{u}} (g : X ⟶ Y) (t : X) :
    ∃ (A : X.Opens) (V' : Y.Opens), IsAffineOpen A ∧ IsAffineOpen V' ∧
      A ≤ g ⁻¹ᵁ V' ∧ t ∈ A := by
  obtain ⟨-, ⟨V', hV', rfl⟩, hvV', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g t)) isOpen_univ
  obtain ⟨-, ⟨A, hA, rfl⟩, htA, hAle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show t ∈ g ⁻¹ᵁ V' from hvV') (g ⁻¹ᵁ V').2
  exact ⟨A, V', hA, hV', hAle, htA⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Joint surjectivity on points -/

/-- A family of morphisms of presheaves on the big fppf site of `S` whose coproduct is
surjective on the points of Tag 03BU is jointly surjective on those points.

Colimits in a category of presheaves of types are computed pointwise, so a section of the
coproduct over an object of the site lies in one summand; the point it represents is therefore
the image of a point of that summand. -/
theorem exists_pointsMap_eq_of_isSurjective_sigmaDesc
    {I : Type u} {V : I → BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ψ : ∀ i, yoneda.obj (V i) ⟶ F) (h : IsSurjective B S hS (Sigma.desc ψ))
    (y : points B S hS F) :
    ∃ (i : I) (c : points B S hS (yoneda.obj (V i))),
      pointsMap B S hS (yoneda.obj (V i)) (ψ i) c = y := by
  obtain ⟨z, hz⟩ := h y
  obtain ⟨q, rfl⟩ := Quot.exists_rep z
  have hcolim := isColimitOfPreserves
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (Opposite.op q.siteObject))
    (colimit.isColimit (Discrete.functor fun i => yoneda.obj (V i)))
  obtain ⟨j, s, hs⟩ := Types.jointly_surjective_of_isColimit hcolim q.value
  have hs' : (Sigma.ι (fun i => yoneda.obj (V i)) j.as).app
      (Opposite.op q.siteObject) s = q.value := by
    simpa using hs
  refine ⟨j.as, (⟨q.carrier, q.contained, q.toBase, s⟩ :
    FieldValuedPoint B S hS (yoneda.obj (V j.as))).class B S hS _, ?_⟩
  rw [← Sigma.ι_desc ψ j.as, pointsMap_comp_apply, pointsMap_class]
  refine hz.symm ▸ congrArg (pointsMap B S hS _ (Sigma.desc ψ)) ?_
  show (FieldValuedPoint.map B S hS (yoneda.obj (V j.as))
    (Sigma.ι (fun i => yoneda.obj (V i)) j.as)
      ⟨q.carrier, q.contained, q.toBase, s⟩).class B S hS _ = _
  obtain ⟨carrier, contained, toBase, value⟩ := q
  congr 1
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  exact hs'

/-! ### The substance of Stacks 03JS -/

/-- Given a commutative square `q ≫ φ = p ≫ ψ` of representable presheaves on the big fppf site
of `S` with `p` étale on underlying schemes, and an affine open `A` of the source of `p` which
`p` carries into an affine open, the `q`-image of the points in `A` meets the chart fibre of `φ`
above `x` in a finite set as soon as the chart fibre of `ψ` above `x` is finite. -/
theorem finite_image_inter_chartFibre
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : points B S hS F}
    {T U V : BigFppfOver B S hS} {q : T ⟶ U} {p : T ⟶ V}
    {φ : yoneda.obj U ⟶ F} {ψ : yoneda.obj V ⟶ F} (hw : yoneda.map q ≫ φ = yoneda.map p ≫ ψ)
    [Etale ((BigFppfOver.toScheme B S hS).map p)] (hfin : (chartFibre B S hS F ψ x).Finite)
    {A : ((BigFppfOver.toScheme B S hS).obj T).Opens} (hA : IsAffineOpen A)
    {V' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (hV' : IsAffineOpen V')
    (hle : A ≤ (BigFppfOver.toScheme B S hS).map p ⁻¹ᵁ V') :
    (pointsMap B S hS (yoneda.obj T) (yoneda.map q) ''
      (pointsToScheme B S hS T ⁻¹' (A : Set _)) ∩ chartFibre B S hS F φ x).Finite := by
  set e := pointsEquivScheme B S hS T
  set Ssub : Set (points B S hS (yoneda.obj T)) :=
    pointsToScheme B S hS T ⁻¹' (A : Set _) ∩
      pointsMap B S hS (yoneda.obj T) (yoneda.map p) ⁻¹' chartFibre B S hS F ψ x
  have hsub : pointsMap B S hS (yoneda.obj T) (yoneda.map q) ''
      (pointsToScheme B S hS T ⁻¹' (A : Set _)) ∩ chartFibre B S hS F φ x ⊆
        pointsMap B S hS (yoneda.obj T) (yoneda.map q) '' Ssub := by
    rintro b ⟨⟨w, hwA, rfl⟩, hbx⟩
    refine ⟨w, ⟨hwA, ?_⟩, rfl⟩
    change pointsMap B S hS (yoneda.obj V) ψ
      (pointsMap B S hS (yoneda.obj T) (yoneda.map p) w) = x
    rw [← pointsMap_apply_comm B S hS hw w]
    exact hbx
  have himage : e '' Ssub ⊆ (BigFppfOver.toScheme B S hS).map p ⁻¹'
      (pointsToScheme B S hS V '' chartFibre B S hS F ψ x) ∩ (A : Set _) := by
    rintro - ⟨w, ⟨hwA, hwF⟩, rfl⟩
    exact ⟨⟨pointsMap B S hS (yoneda.obj T) (yoneda.map p) w, hwF,
      pointsToScheme_pointsMap_yoneda B S hS p w⟩, hwA⟩
  refine ((Set.Finite.of_finite_image ?_ e.injective.injOn).image _).subset hsub
  exact (finite_inter_preimage_of_etale _ hA hV' hle (hfin.image _)).subset himage

/-- **The substance of Stacks 03JS.** Let `F` be a presheaf on the big fppf site of `S` and let
`x` be a point of `|F|`. Let `ψ i : h_{V i} ⟶ F` be a family of étale morphisms which is jointly
surjective on points and for which the fibre of `|V i| → |F|` above `x` is finite for every `i`.
Then the fibre of `|U| → |F|` above `x` is finite for every étale `φ : h_U ⟶ F` whose source has
quasi-compact underlying scheme.

Neither `F` nor the sources are required to be algebraic spaces; only étaleness of the charts,
which already carries representability of their base changes, is used. -/
theorem finite_chartFibre_of_jointlySurjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : points B S hS F}
    {I : Type*} {V : I → BigFppfOver B S hS} {ψ : ∀ i, yoneda.obj (V i) ⟶ F}
    (hψ : ∀ i, IsEtale B S hS (ψ i))
    (hcov : ∀ y : points B S hS F,
      ∃ i, y ∈ Set.range (pointsMap B S hS (yoneda.obj (V i)) (ψ i)))
    (hfin : ∀ i, (chartFibre B S hS F (ψ i) x).Finite)
    {U : BigFppfOver B S hS} (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ) :
    (chartFibre B S hS F φ x).Finite := by
  classical
  have hφp := presheaf_etale_of_isEtale B S hS hφ
  -- The representable fibre products `W i = h_U ×_F h_{V i}` and their two projections.
  set T : I → BigFppfOver B S hS := fun i => hφp.rep.pullback (ψ i)
  set pr : ∀ i, T i ⟶ V i := fun i => hφp.rep.snd (ψ i)
  set qr : ∀ i, T i ⟶ U := fun i => hφp.rep.fst' (ψ i)
  have hsq : ∀ i, IsPullback (yoneda.map (qr i)) (yoneda.map (pr i)) φ (ψ i) := fun i =>
    hφp.rep.isPullback' (ψ i)
  have hprEt : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (pr i)) := fun i =>
    hφp.property_snd (ψ i)
  have hqrEt : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (qr i)) := fun i =>
    (presheaf_etale_of_isEtale B S hS (hψ i)).property φ (yoneda.map (pr i)) (qr i) (hsq i).flip
  have hqrOpen : ∀ i,
      IsOpenMap (pointsMap B S hS (yoneda.obj (T i)) (yoneda.map (qr i))) := fun i =>
    isOpenMap_pointsMap_of_presheafEtale B S hS _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (qr i)).2 (hqrEt i))
  -- Every point of `|U|` lies in the `q i`-image of an affine open of some `W i` which `p i`
  -- carries into an affine open of `V i`.
  have hchoice : ∀ a : points B S hS (yoneda.obj U), ∃ (i : I)
      (A : ((BigFppfOver.toScheme B S hS).obj (T i)).Opens)
      (V' : ((BigFppfOver.toScheme B S hS).obj (V i)).Opens),
      IsAffineOpen A ∧ IsAffineOpen V' ∧
      A ≤ (BigFppfOver.toScheme B S hS).map (pr i) ⁻¹ᵁ V' ∧
      a ∈ pointsMap B S hS (yoneda.obj (T i)) (yoneda.map (qr i)) ''
        (pointsToScheme B S hS (T i) ⁻¹' (A : Set _)) := by
    intro a
    obtain ⟨i, c, hc⟩ := hcov (pointsMap B S hS (yoneda.obj U) φ a)
    obtain ⟨w, hw₁, -⟩ := exists_points_of_isPullback B S hS (hsq i) a c hc.symm
    obtain ⟨A, V', hA, hV', hAle, htA⟩ := exists_isAffineOpen_le_preimage
      ((BigFppfOver.toScheme B S hS).map (pr i)) (pointsToScheme B S hS (T i) w)
    exact ⟨i, A, V', hA, hV', hAle, w, htA, hw₁⟩
  choose idx aff affTarget hAff hAffTarget hLe hMem using hchoice
  -- The chosen images form an open cover of the quasi-compact point space `|U|`.
  set O : points B S hS (yoneda.obj U) → Set (points B S hS (yoneda.obj U)) := fun a =>
    pointsMap B S hS (yoneda.obj (T (idx a))) (yoneda.map (qr (idx a))) ''
      (pointsToScheme B S hS (T (idx a)) ⁻¹' ((aff a : Set _)))
  have hOopen : ∀ a, IsOpen (O a) := fun a => hqrOpen (idx a) _ <| by
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS (T (idx a)))]
    exact (aff a).2
  have := @compactSpace_points_yoneda B S hS U hU
  obtain ⟨fs, hfs⟩ := isCompact_univ.elim_finite_subcover O hOopen
    (fun a _ => Set.mem_iUnion.2 ⟨a, hMem a⟩)
  -- Each piece of the cover meets the chart fibre in a finite set.
  have hpiece : ∀ a, (O a ∩ chartFibre B S hS F φ x).Finite := fun a =>
    have := hprEt (idx a)
    finite_image_inter_chartFibre B S hS (x := x) (hsq (idx a)).w (hfin _) (hAff a)
      (hAffTarget a) (hLe a)
  refine (fs.finite_toSet.biUnion fun a _ => hpiece a).subset fun b hb => ?_
  obtain ⟨a, ha, hba⟩ := Set.mem_iUnion₂.1 (hfs (Set.mem_univ b))
  exact Set.mem_iUnion₂.2 ⟨a, ha, hba, hb⟩

/-! ### The two implications of Stacks 03JS -/

/-- **Stacks 03JS, part (1) implies part (2).** If some family of étale charts of an algebraic
space `F` over `S` whose coproduct is surjective has finite chart fibres above a point `x` of
`|F|`, then every étale chart of `F` with affine source has a finite chart fibre above `x`.

The family is used only through joint surjectivity on points, which is what surjectivity of the
coproduct gives by `AlgebraicGeometry.Space.exists_pointsMap_eq_of_isSurjective_sigmaDesc`, and
affineness of the chart is used only through quasi-compactness of its underlying scheme; the
general statement is `AlgebraicGeometry.Space.finite_chartFibre_of_jointlySurjective`. -/
@[stacks 03JS "part (1) implies part (2)"]
theorem finite_chartFibre_of_etaleCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {x : points B S hS F}
    {I : Type u} {V : I → BigFppfOver B S hS} (ψ : ∀ i, yoneda.obj (V i) ⟶ F)
    (hψ : ∀ i, IsEtale B S hS (ψ i)) (hsurj : IsSurjective B S hS (Sigma.desc ψ))
    (hfin : ∀ i, (chartFibre B S hS F (ψ i) x).Finite)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ F) (hφ : IsEtale B S hS φ) :
    (chartFibre B S hS F φ x).Finite :=
  finite_chartFibre_of_jointlySurjective B S hS hψ
    (exists_pointsMap_eq_of_isSurjective_sigmaDesc B S hS ψ hsurj) hfin inferInstance hφ

/-- **Stacks 03JS, part (2) implies part (1).** An algebraic space over `S` has an étale
covering family by affine schemes, so if every étale chart with affine source has a finite chart
fibre above a point `x` of `|F|`, then the members of one covering family do.

The covering family is the one of Stacks 03FX
(`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`), exactly as in
`AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover`,
whose surjectivity argument this repeats. -/
@[stacks 03JS "part (2) implies part (1)"]
theorem exists_etaleCover_finite_chartFibre
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : ∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ φ : yoneda.obj U ⟶ F, IsEtale B S hS φ → (chartFibre B S hS F φ x).Finite) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (ψ : ∀ i, yoneda.obj (V i) ⟶ F),
      (∀ i, IsEtale B S hS (ψ i)) ∧ IsSurjective B S hS (Sigma.desc ψ) ∧
      ∀ i, (chartFibre B S hS F (ψ i) x).Finite := by
  obtain ⟨U, f, I, W, j, e, hfS, -, hWaff, hje, -, hjE, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  refine ⟨I, W, fun i => yoneda.map (j i) ≫ f,
    fun i => isEtale_of_presheaf_etale B S hS (hjE i), fun y => ?_,
    fun i => h (W i) (hWaff i) _ (isEtale_of_presheaf_etale B S hS (hjE i))⟩
  obtain ⟨u, hu⟩ := isSurjective_of_presheafSurjective B S hS f hfS y
  obtain ⟨i, w, hw⟩ : ∃ (i : I) (w : (BigFppfOver.toScheme B S hS).obj (W i)),
      (BigFppfOver.toScheme B S hS).map (j i) w = pointsToScheme B S hS U u := by
    set z := (sigmaMk fun k => (BigFppfOver.toScheme B S hS).obj (W k)).symm
      (e.inv (pointsToScheme B S hS U u)) with hz
    refine ⟨z.1, z.2, ?_⟩
    have hι : Sigma.ι (fun k => (BigFppfOver.toScheme B S hS).obj (W k)) z.1 z.2 =
        e.inv (pointsToScheme B S hS U u) := by
      rw [← sigmaMk_mk, hz, Homeomorph.apply_symm_apply]
    rw [← hje z.1, Scheme.Hom.comp_apply, hι, ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  obtain ⟨a, ha⟩ := surjective_pointsToScheme B S hS (W i) w
  have hau : pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i)) a = u :=
    injective_pointsToScheme B S hS U
      (by rw [pointsToScheme_pointsMap_yoneda B S hS (j i) a, ha, hw])
  refine ⟨pointsMap B S hS (yoneda.obj (W i))
    (Sigma.ι (fun k => yoneda.obj (W k)) i) a, ?_⟩
  rwa [← pointsMap_comp_apply, Sigma.ι_desc, pointsMap_comp_apply, hau]

end Space

end AlgebraicGeometry

end

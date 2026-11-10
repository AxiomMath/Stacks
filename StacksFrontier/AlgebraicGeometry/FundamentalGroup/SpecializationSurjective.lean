module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.HomotopySequenceExactness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.FinitePointKernel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.GeometricallyUnibranch
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianClosedGeometricFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.OpenLocus
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.RelativeDimension

/-!
# Surjectivity of the specialization map

Let `f : X ⟶ S` be a flat proper morphism with geometrically connected fibres and let
`s' ⇝ s` be a specialization of points of `S`. If the fibre `X_s` is geometrically reduced, then
every specialization map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` is surjective.

The specialization map is built from the strict henselization `A` of `𝒪_{S,s}`: both geometric
points factor through `Spec A`, base change along `X_{s̄} ⟶ X_A` is an equivalence on finite
étale covers, and `sp` is the resulting composite `π₁(X_{s̄'}) ⟶ π₁(X_A) = π₁(X_{s̄})`. So
surjectivity of `sp` is surjectivity of `π₁(X_{s̄'}) ⟶ π₁(X_A)`.

Geometric reducedness of `X_s` propagates to every fibre of `X_A ⟶ Spec A`: the locus of points
of `S` with geometrically reduced fibre is open, and `Spec A ⟶ S` lands in the generizations of
`s`, each of which lies in every open set containing `s`. The fibres of `X_A ⟶ Spec A` are
therefore geometrically connected and geometrically reduced, and `A` is strictly henselian, so a
connected finite étale cover of `X_A` which acquires a section over the geometric fibre is the
base change of a finite étale cover of `Spec A`; that cover splits, so the section extends and
the original cover has a section over `X_A` already. This is the lifting criterion for
surjectivity of the map induced by a geometric fibre.

## Main results

* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_geometricFibre_of_strictlyHenselian`:
  for a flat proper morphism of finite presentation with geometrically connected and
  geometrically reduced fibres over a strictly henselian local base, the map
  `π₁(X_b̄) ⟶ π₁(X)` induced by a geometric fibre is surjective.
* `AlgebraicGeometry.isSpecializationMap_of_isStrictHenselization`: the data of the construction
  — a strict henselization `A` of `𝒪_{S,s}`, factorizations of the two geometric points through
  `Spec A` with `s̄` over the closed point, and a homomorphism satisfying the defining equation —
  already exhibits a specialization map: connectedness of `X_A` and the identification
  `π₁(X_A) = π₁(X_{s̄})` are consequences, not further requirements.
* `AlgebraicGeometry.surjective_specializationMap_of_properFlat`: surjectivity of the
  specialization map of a flat proper morphism of finite presentation with geometrically
  connected fibres, one of whose fibres is geometrically reduced.
* `AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat`: the same conclusion for a
  flat proper morphism, with no finiteness hypothesis beyond properness.

## Implementation notes

The predicate `AlgebraicGeometry.IsSpecializationMap` records, besides the data of the source's
construction, two statements which the source proves rather than assumes: that `X_A` is connected,
and that base change along `X_{s̄} ⟶ X_A` is an equivalence on finite étale covers — the second
equality in the source's composite `π₁(X_{s̄'}) ⟶ π₁(X_A) = π₁(X_{κ(s)^{sep}}) = π₁(X_{s̄})`,
which is Stacks 0A48 followed by Stacks 0BTW and 0A49. So the surjectivity statement is not
phrased with that predicate as an input: `isSpecializationMap_of_isStrictHenselization` derives
both from properness and geometrically connected fibres, and
`surjective_specializationMap_of_properFlat` asks only for the construction's data and the
defining equation of `sp`.

Openness of the geometrically reduced fibre locus and exactness of the homotopy sequence are both
available only for a morphism of finite presentation, and over a general base a flat proper
morphism need not be locally of finite presentation. The hypothesis is removed by base changing
to a strictly henselian valuation ring over which the given specialization map is realized: over
a valuation ring a flat morphism of finite type is automatically of finite presentation, and the
base is a local scheme, so an open subset of it containing the closed point is everything and the
geometrically reduced fibre locus needs no shrinking.

## References

* [Stacks Project, Tag 0C0P](https://stacks.math.columbia.edu/tag/0C0P)
* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
* [Stacks Project, Tag 0C0J](https://stacks.math.columbia.edu/tag/0C0J)
* [Stacks Project, Tag 0C0E](https://stacks.math.columbia.edu/tag/0C0E)
* [Stacks Project, Tag 053E](https://stacks.math.columbia.edu/tag/053E)
* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### The geometric fibre over a strictly henselian local base -/

/-- **A finite étale cover of a scheme over a strictly henselian local ring which is a base
change and has a section over a connected scheme has a section.** If the finite étale cover
`V ⟶ W` is the base change of a finite étale cover `U ⟶ Spec R`, with `R` henselian local with
separably closed residue field, and `V` has a section over a connected scheme `P` mapping to
`W`, then `V ⟶ W` has a section.

The section over `P` lands in `U`, hence extends to a section of `U ⟶ Spec R`, whose base change
is a section of `V ⟶ W`. -/
private theorem nonempty_hom_finiteEtaleOverTerminal_of_essImage_of_section
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    {W : Scheme.{u}} (h : W ⟶ Spec (.of R)) (V : FiniteEtaleOver W)
    (U : FiniteEtaleOver (Spec (.of R))) (e : (finiteEtaleBaseChange h).obj U ≅ V)
    (P : Scheme.{u}) [ConnectedSpace ↥P] (k : P ⟶ W) (q : P ⟶ V.left) (hq : q ≫ V.hom = k) :
    Nonempty (finiteEtaleOverTerminal W ⟶ V) := by
  have heinv : e.inv.left ≫ ((finiteEtaleBaseChange h).obj U).hom = V.hom :=
    MorphismProperty.Over.w e.inv
  have hehom : e.hom.left ≫ V.hom = ((finiteEtaleBaseChange h).obj U).hom :=
    MorphismProperty.Over.w e.hom
  have hm : (q ≫ e.inv.left ≫ finiteEtaleBaseChangeProj h U) ≫ U.hom = k ≫ h := by
    simp only [Category.assoc]
    rw [finiteEtaleBaseChangeProj_comp_hom h U,
      ← Category.assoc e.inv.left ((finiteEtaleBaseChange h).obj U).hom h, heinv,
      ← Category.assoc q V.hom h, hq]
  obtain ⟨t, ht, -⟩ :=
    exists_section_of_henselian_of_isSepClosed R U P (k ≫ h) _ hm
  have hlift : (h ≫ t) ≫ U.hom = 𝟙 W ≫ h := by
    rw [Category.assoc, ht, Category.comp_id, Category.id_comp]
  refine ⟨MorphismProperty.Over.homMk
    (finiteEtaleBaseChangeLift h U (h ≫ t) (𝟙 W) hlift ≫ e.hom.left) ?_⟩
  change (finiteEtaleBaseChangeLift h U (h ≫ t) (𝟙 W) hlift ≫ e.hom.left) ≫ V.hom = 𝟙 W
  rw [Category.assoc, hehom, finiteEtaleBaseChangeLift_comp_hom]

/-- **A connected finite étale cover with a section over a geometric fibre has a section.** Let
`R` be a henselian local ring with separably closed residue field and let `h : W ⟶ Spec R` be
flat, proper, of finite presentation, with geometrically connected and geometrically reduced
fibres. A connected finite étale cover of `W` whose restriction to the geometric fibre `W_b̄`
admits a section already admits a section over `W`.

The cover is the base change of a finite étale cover of `Spec R`, by the Stein factorization
argument of the homotopy sequence; the section over the connected `W_b̄` then extends over the
strictly henselian base. -/
private theorem nonempty_hom_finiteEtaleOverTerminal_of_section_geometricFibre
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    {W : Scheme.{u}} (h : W ⟶ Spec (.of R)) [IsProper h] [Flat h]
    [GeometricallyReduced h] [GeometricallyConnected h] (hfp : FinitePresentation h)
    (b : GeometricPoint (Spec (.of R))) (w : GeometricPoint (pullback h b.hom))
    (V : FiniteEtaleOver W) (hV : PreGaloisCategory.IsConnected V)
    (hsec : Nonempty (finiteEtaleOverTerminal (pullback h b.hom) ⟶
      (finiteEtaleBaseChange (pullback.fst h b.hom)).obj V)) :
    Nonempty (finiteEtaleOverTerminal W ⟶ V) := by
  obtain ⟨c⟩ := hsec
  obtain ⟨U, ⟨e⟩⟩ :=
    essImage_finiteEtaleBaseChange_of_isConnected_of_section h hfp b w V hV
      ⟨finiteEtaleOverTerminal (pullback h b.hom),
        ⟨MorphismProperty.Over.mkIdTerminal _ _⟩, ⟨c⟩⟩
  have hc : c.left ≫ ((finiteEtaleBaseChange (pullback.fst h b.hom)).obj V).hom = 𝟙 _ :=
    MorphismProperty.Over.w c
  have hq : (c.left ≫ finiteEtaleBaseChangeProj (pullback.fst h b.hom) V) ≫ V.hom
      = pullback.fst h b.hom := by
    rw [Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc, hc]
    exact Category.id_comp (pullback.fst h b.hom)
  have : ConnectedSpace ↥(pullback h b.hom) := connectedSpace_fiberOverGeometricPoint h b
  exact nonempty_hom_finiteEtaleOverTerminal_of_essImage_of_section h V U e
    (pullback h b.hom) (pullback.fst h b.hom) _ hq

/-- **The geometric fibre of a proper flat family over a strictly henselian local base is
π₁-surjective.** Let `R` be a henselian local ring with separably closed residue field and let
`h : W ⟶ Spec R` be flat, proper, of finite presentation, with geometrically connected and
geometrically reduced fibres. For every geometric point `b̄` of `Spec R` and every geometric
point `w` of the geometric fibre `W_b̄`, the induced map

```
π₁(W_b̄, w) ⟶ π₁(W, w)
```

is surjective.

This is the exactness of the homotopy sequence of `h` together with the triviality of
`π₁(Spec R)`, in the form of the lifting criterion for surjectivity. -/
@[sga "1 X 1.4" "special case",
  sga "1 XIII 4.1" "special case",
  sga "1 XIII 4.2" "special case",
  sga "1 XIII 4.4" "special case"]
theorem surjective_etaleFundamentalGroupMap_geometricFibre_of_strictlyHenselian
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    {W : Scheme.{u}} (h : W ⟶ Spec (.of R)) [IsProper h] [Flat h]
    [GeometricallyReduced h] [GeometricallyConnected h] (hfp : FinitePresentation h)
    [ConnectedSpace ↥W] (b : GeometricPoint (Spec (.of R)))
    (w : GeometricPoint (pullback h b.hom)) :
    Function.Surjective (etaleFundamentalGroupMap (pullback.fst h b.hom) w) := by
  have : ConnectedSpace ↥(pullback h b.hom) := connectedSpace_fiberOverGeometricPoint h b
  exact surjective_etaleFundamentalGroupMap_of_section_lifting (pullback.fst h b.hom) w
    (fun V hV hsec ↦
      nonempty_hom_finiteEtaleOverTerminal_of_section_geometricFibre h hfp b w V hV hsec)

/-! ### Spreading geometric reducedness of one fibre over a base change -/

/-- The fibre of `X ×_S T ⟶ T` at `u` is geometrically reduced iff the fibre of `X ⟶ S` at
`g u` is. -/
private theorem geometricallyReduced_pullback_snd_fiber_iff {X S T : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (u : T) :
    GeometricallyReduced ((pullback.snd f g).fiberToSpecResidueField u) ↔
      GeometricallyReduced (f.fiberToSpecResidueField (g u)) :=
  Set.ext_iff.mp (geometricallyReduced_fiber_set_eq_preimage_of_isPullback f (pullback.snd f g)
    (pullback.fst f g) g (IsPullback.of_hasPullback f g)) u

/-- **A base change landing in the generizations of a point with geometrically reduced fibre has
geometrically reduced fibres.** Let `f : X ⟶ S` be flat, proper and of finite presentation, let
`z ∈ S` be a point whose fibre `X_z` is geometrically reduced, and let `g : T ⟶ S` be a morphism
every point of whose image is a generization of `z`. Then every fibre of `X ×_S T ⟶ T` is
geometrically reduced.

The locus of points of `S` with geometrically reduced fibre is open and compatible with base
change; an open set containing `z` contains every generization of `z`. -/
theorem geometricallyReduced_pullback_snd_of_specializes {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f) (g : T ⟶ S) (z : S)
    (hz : GeometricallyReduced (f.fiberToSpecResidueField z)) (hg : ∀ u : T, g u ⤳ z) :
    GeometricallyReduced (pullback.snd f g) := by
  rw [GeometricallyReduced.iff_geometricallyReduced_fiber]
  intro u
  exact (geometricallyReduced_pullback_snd_fiber_iff f g u).2
    ((hg u).mem_open (isOpen_geometricallyReduced_fiber f hfp) hz)

/-! ### Surjectivity of a specialization map -/

/-- **Surjectivity of a composite on étale fundamental groups.** The map induced by `a ≫ b` is
the composite of the maps induced by `a` and by `b`, read through the comparison
`AlgebraicGeometry.fiberFunctorMapCompIso` of the two descriptions of the image base point. -/
private theorem surjective_etaleFundamentalGroupMap_comp_of_surjective
    {A B C : Scheme.{u}} [ConnectedSpace ↥A] [ConnectedSpace ↥B] [ConnectedSpace ↥C]
    (a : A ⟶ B) (b : B ⟶ C) (q : GeometricPoint A)
    (ha : Function.Surjective (etaleFundamentalGroupMap a q))
    (hb : Function.Surjective (etaleFundamentalGroupMap b (q.map a))) :
    Function.Surjective (etaleFundamentalGroupMap (a ≫ b) q) := by
  intro ρ
  obtain ⟨τ, hτ⟩ := hb (etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso a b q) ρ)
  obtain ⟨σ, hσ⟩ := ha τ
  refine ⟨σ, (etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso a b q)).injective ?_⟩
  rw [etaleFundamentalGroupMulEquiv_mapCompIso, hσ, hτ]

/-- **Surjectivity of a map which the predicate `IsSpecializationMap` recognises.** Let
`f : X ⟶ S` be flat, proper, of finite presentation, with geometrically connected fibres, let
`s'` and `s` be geometric points of `S` with `X_s` geometrically reduced, and let
`sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` be a specialization map. Then `sp` is surjective.

This is not the form in which Stacks 0C0P is registered: `IsSpecializationMap` records, besides
the data of the construction, that `X_A` is connected and that base change along `X_{s̄} ⟶ X_A`
is an equivalence on finite étale covers, both of which the source proves. The tag sits on
`AlgebraicGeometry.surjective_specializationMap_of_properFlat`, which asks only for the data and
derives those two.

The specialization map factors as `π₁(X_{s̄'}) ⟶ π₁(X_A) = π₁(X_{s̄})` for `A` the strict
henselization of `𝒪_{S,s}`, the second map being an isomorphism; so it suffices to see that
`π₁(X_{s̄'}) ⟶ π₁(X_A)` is surjective. The fibres of `X_A ⟶ Spec A` are the fibres of `f` at
generizations of `s`, which are geometrically reduced because the geometrically reduced fibre
locus is open, and they are geometrically connected; the homotopy sequence of `X_A ⟶ Spec A`
together with the triviality of `π₁(Spec A)` gives the surjectivity. -/
@[sga "1 X 3.8" "more general"]
theorem surjective_isSpecializationMap_of_properFlat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] (hfp : FinitePresentation f)
    (s' s : GeometricPoint S)
    (hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (closedPoint s.residueField))))
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp) :
    Function.Surjective sp := by
  classical
  simp only [IsSpecializationMap] at hsp
  obtain ⟨A, hAring, hAloc, hAalg, ⟨hstrict⟩, p', hp', p, hp, hclosed, hXA, hi, t, hform⟩ := hsp
  let := hAring
  let := hAloc
  let := hAalg
  let := hstrict.henselian
  let := hstrict.sepClosed
  have : IsSepClosed (ResidueField A) := isSepClosed_residueField_of_maximalIdeal A
  let z : S := s.hom (closedPoint s.residueField)
  let gA : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫ S.fromSpecStalk z
  let fA := pullback.snd f gA
  let : ConnectedSpace (pullback f gA : Scheme.{u}) := hXA
  have := hi
  -- the base change to the strict henselization is again proper, flat and finitely presented
  have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  have : QuasiCompact f := hfp.quasiCompact
  have : QuasiSeparated f := hfp.quasiSeparated
  have hfpA : FinitePresentation fA := ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsProper fA := inferInstanceAs (IsProper (pullback.snd f gA))
  have : Flat fA := inferInstanceAs (Flat (pullback.snd f gA))
  have : GeometricallyConnected fA :=
    inferInstanceAs (GeometricallyConnected (pullback.snd f gA))
  -- and has geometrically reduced fibres, the base mapping into the generizations of `z`
  have hgen : ∀ a : Spec (.of A), gA a ⤳ z := by
    intro a
    have : gA a ∈ Set.range (S.fromSpecStalk z).base :=
      ⟨(Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A))) a, rfl⟩
    rwa [S.range_fromSpecStalk] at this
  have : GeometricallyReduced fA :=
    geometricallyReduced_pullback_snd_of_specializes f hfp gA z hred hgen
  -- the generic geometric point, read on `Spec A`
  let sA' : GeometricPoint (Spec (.of A)) := { residueField := s'.residueField, hom := p' }
  have : ConnectedSpace ↥(pullback fA sA'.hom) := connectedSpace_fiberOverGeometricPoint fA sA'
  -- the geometric fibre `X_{s̄'} ⟶ X_A` is an isomorphism followed by a fibre projection
  have he : fiberOverGeometricPointMap f s' gA p' hp'
      = ((pullback.congrHom rfl hp'.symm).hom ≫ (pullbackLeftPullbackSndIso f gA p').inv) ≫
        pullback.fst (pullback.snd f gA) p' := by
    refine pullback.hom_ext ?_ ?_
    · simp only [fiberOverGeometricPointMap, pullback.map, Category.comp_id, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom]
      rw [pullback.lift_fst, pullback.lift_fst]
    · simp only [fiberOverGeometricPointMap, pullback.map, Category.comp_id, Category.assoc,
        pullback.congrHom_hom]
      rw [pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd]
  have hsurj : Function.Surjective
      (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' gA p' hp') x') := by
    rw [he]
    exact surjective_etaleFundamentalGroupMap_comp_of_surjective _ _ x'
      (surjective_etaleFundamentalGroupMap_of_isIso _ x')
      (surjective_etaleFundamentalGroupMap_geometricFibre_of_strictlyHenselian fA hfpA sA' _)
  -- transport the surjectivity across the identification `π₁(X_A) = π₁(X_{s̄})`
  intro ρ
  obtain ⟨γ, hγ⟩ := hsurj ((etaleFundamentalGroupMulEquiv t).symm
    (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s gA p hp) x ρ))
  refine ⟨γ, (bijective_etaleFundamentalGroupMap_of_isEquivalence
    (fiberOverGeometricPointMap f s gA p hp) x).1 ?_⟩
  rw [hform γ, hγ, (etaleFundamentalGroupMulEquiv t).apply_symm_apply]

/-! ### The construction of the specialization map, with its two lemmas discharged -/

/-- The structure morphism `Spec A ⟶ S` of an algebra `A` over the local ring of `S` at a point
`z`: the spectrum of `A` over the spectrum of the stalk, followed by the canonical morphism of
the stalk's spectrum to `S`. For `A` a strict henselization of `𝒪_{S,z}` this is the morphism
through which the geometric points are factored in the construction of a specialization map. -/
abbrev specStalkAlgebraHom (S : Scheme.{u}) (z : S) (A : Type u) [CommRing A]
    [Algebra (S.presheaf.stalk z) A] : Spec (.of A) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫ S.fromSpecStalk z

/-- **The data of the construction already exhibits a specialization map.** Let `f : X ⟶ S` be
proper with geometrically connected fibres, let `s'` and `s` be geometric points of `S`, let `A`
be a strict henselization of `𝒪_{S,s}` relative to a separable closure of `κ(s)`, let
`p' : s̄' ⟶ Spec A` and `p : s̄ ⟶ Spec A` be factorizations of the two geometric points over `S`
with `p` landing on the closed point, and let `sp` satisfy the defining equation of the
specialization map against a fibre-functor isomorphism `t` on `X_A`. Then
`AlgebraicGeometry.IsSpecializationMap f s' s x' x sp` holds.

The two clauses of that predicate which are statements rather than data are consequences of the
hypotheses here: `X_A` is connected because `f` is proper with geometrically connected fibres and
`Spec A` is connected, and base change along `X_{s̄} ⟶ X_A` is an equivalence on finite étale
covers because `A` is strictly henselian and `p` lands on its closed point. -/
theorem isSpecializationMap_of_isStrictHenselization {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (SeparableClosure
        (maximalIdeal (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField) A)
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (hclosed : p (closedPoint s.residueField) = closedPoint A)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        IsSpecializationMap f s' s x' x sp := by
  intro t hform
  have := hA.henselian
  have := hA.sepClosed
  have : IsSepClosed (ResidueField A) := isSepClosed_residueField_of_maximalIdeal A
  exact ⟨A, inferInstance, inferInstance, inferInstance, ⟨hA⟩, p', hp', p, hp, hclosed,
    connectedSpace_pullback_spec_of_isProper f A _,
    isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap f s A _ p hp hclosed,
    t, hform⟩

/-- **Surjectivity of a specialization map of a flat proper morphism of finite presentation.**
Let `f : X ⟶ S` be a flat proper morphism of finite presentation with geometrically connected
fibres and let `s' ⇝ s` be a specialization of points of `S`, realized as in the construction of
the specialization map: `A` is a strict henselization of `𝒪_{S,s}` relative to a separable
closure of `κ(s)`, and the two geometric points are factored through `Spec A`, the special one
over the closed point. Let

```
sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})
```

be the resulting specialization map, that is, a continuous homomorphism satisfying the equation
defining it against the canonical maps to `π₁(X_A)`. If the fibre `X_s` is geometrically reduced,
then `sp` is surjective.

The composite `π₁(X_{s̄'}) ⟶ π₁(X_A) = π₁(X_{s̄})` has an isomorphism for its second map, so it
suffices to see that `π₁(X_{s̄'}) ⟶ π₁(X_A)` is surjective. The fibres of `X_A ⟶ Spec A` are the
fibres of `f` at generizations of `s`, which are geometrically reduced because the geometrically
reduced fibre locus is open, and they are geometrically connected; the homotopy sequence of
`X_A ⟶ Spec A` together with the triviality of `π₁(Spec A)` gives the surjectivity.

Finite presentation is not needed for this conclusion:
`AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat` proves it from flatness and
properness alone, by reducing to a valuation-ring base where finite presentation is automatic.
Over a general base it is a genuine extra hypothesis, flat and proper not implying locally of
finite presentation there. -/
@[sga "1 X 2.4" "more general"]
theorem surjective_specializationMap_of_properFlat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] (hfp : FinitePresentation f)
    (s' s : GeometricPoint S)
    (hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (closedPoint s.residueField))))
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (SeparableClosure
        (maximalIdeal (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField) A)
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (hclosed : p (closedPoint s.residueField) = closedPoint A)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        Function.Surjective sp := by
  intro t hform
  exact surjective_isSpecializationMap_of_properFlat f hfp s' s hred x' x sp
    (isSpecializationMap_of_isStrictHenselization f s' s A hA p' hp' p hp hclosed x' x sp t hform)

/-! ### Surjectivity with no finiteness hypothesis beyond properness -/

/-- **A flat proper scheme over a valuation ring is of finite presentation.** Properness makes
the morphism locally of finite type, quasi-compact and quasi-separated; over a valuation ring a
flat algebra of finite type is finitely presented, so the morphism is locally of finite
presentation as well. -/
private theorem finitePresentation_of_flat_isProper_spec_valuationRing {R : Type u} [CommRing R]
    [IsDomain R] [ValuationRing R] {W : Scheme.{u}} (h : W ⟶ Spec (.of R)) [Flat h] [IsProper h] :
    FinitePresentation h :=
  ⟨locallyOfFinitePresentation_of_flat_over_valuationRing h, inferInstance, inferInstance⟩

/-- **Surjectivity of a specialization map of a flat proper morphism, with no finiteness
hypothesis beyond properness.** Let `f : X ⟶ S` be flat and proper with geometrically connected
fibres, let `s'` and `s` be geometric points of `S` with `X_s` geometrically reduced, and let
`sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` be a specialization map. Then `sp` is surjective.

This strengthens `AlgebraicGeometry.surjective_isSpecializationMap_of_properFlat` by dropping
its hypothesis that `f` be of finite presentation, which does not follow from flatness and
properness over a general base.

Every specialization map is isomorphic to one over a strictly henselian valuation ring: there
are a strictly henselian valuation ring `R` with algebraically closed fraction field and a
morphism `r : Spec R ⟶ S` taking the generic point of `Spec R` to the image of `s̄'` and the
closed point to the image of `s̄`, such that `sp` is intertwined with a specialization map of the
base change `X_R ⟶ Spec R` by isomorphisms of topological groups. That base change is again flat
and proper with geometrically connected fibres, its fibre over the closed point is a base change
of `X_s` and so geometrically reduced, and over a valuation ring a flat morphism of finite type
is automatically of finite presentation. So the finitely presented case applies to it, and
surjectivity transports back along the two isomorphisms. -/
theorem surjective_isSpecializationMap_of_isProper_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (closedPoint s.residueField))))
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp) :
    Function.Surjective sp := by
  classical
  obtain ⟨R, hRring, hRdom, hRval, -, -, -, r, η, o, yη, yo, spR, -, hoclosed, -, -, -, hro,
    hspR, eη, eo, hcomm⟩ :=
    exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing f s' s x' x sp hsp
  let := hRring
  let := hRdom
  let := hRval
  -- the base change to `Spec R` is flat and proper, hence of finite presentation over the
  -- valuation ring `R`
  have hfpR : FinitePresentation (pullback.snd f r) :=
    finitePresentation_of_flat_isProper_spec_valuationRing (pullback.snd f r)
  -- its fibre over the closed point of `Spec R` is a base change of the geometrically reduced
  -- fibre `X_s`
  have hredR : GeometricallyReduced
      ((pullback.snd f r).fiberToSpecResidueField (o.hom (closedPoint o.residueField))) := by
    have hodef : o.hom (closedPoint o.residueField) = o.hom default :=
      congrArg o.hom (Subsingleton.elim _ _)
    have hsdef : s.hom default = s.hom (closedPoint s.residueField) :=
      congrArg s.hom (Subsingleton.elim _ _)
    rw [geometricallyReduced_pullback_snd_fiber_iff, hodef, hro, hsdef]
    exact hred
  have hsurjR : Function.Surjective spR :=
    surjective_isSpecializationMap_of_properFlat (pullback.snd f r) hfpR η o hredR yη yo spR hspR
  intro ρ
  obtain ⟨σ, hσ⟩ := hsurjR (eo ρ)
  refine ⟨eη.symm σ, eo.injective ?_⟩
  rw [hcomm, eη.apply_symm_apply, hσ]

/-- **Stacks Project, Tag 0C0P.** Let `f : X ⟶ S` be a flat proper morphism with geometrically
connected fibres and let `s' ⇝ s` be a specialization of points of `S`, realized as in the
construction of the specialization map: `A` is a strict henselization of `𝒪_{S,s}` relative to a
separable closure of `κ(s)`, and the two geometric points are factored through `Spec A`, the
special one over the closed point. Let

```
sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})
```

be the resulting specialization map, that is, a continuous homomorphism satisfying the equation
defining it against the canonical maps to `π₁(X_A)`. If the fibre `X_s` is geometrically reduced,
then `sp` is surjective.

No finiteness hypothesis beyond properness is needed. Every specialization map is isomorphic to a
specialization map over a strictly henselian valuation ring `R`, for the base change
`X_R ⟶ Spec R` along a morphism `Spec R ⟶ S` carrying the generic point of `Spec R` to the image
of `s̄'` and the closed point to the image of `s̄`. That base change is flat and proper with
geometrically connected fibres, its closed fibre is geometrically reduced because `X_s` is, and
over a valuation ring a flat morphism of finite type is automatically of finite presentation. So
the geometrically reduced fibre locus of `X_R ⟶ Spec R` is open and contains the closed point of
the local scheme `Spec R`, hence is all of it; the homotopy sequence of `X_R ⟶ Spec R` together
with the triviality of `π₁(Spec R)` makes the specialization map over `R` surjective, and
surjectivity transports back to `sp`.

`AlgebraicGeometry.surjective_specializationMap_of_properFlat` is the same conclusion for a
morphism which is moreover assumed to be of finite presentation. -/
@[stacks 0C0P "the whole statement, under the source's hypotheses only.",
  sga "1 X 2.4" "more general",
  sga "1 X 3.8" "more general"]
theorem surjective_specializationMap_of_isProper_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (closedPoint s.residueField))))
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (SeparableClosure
        (maximalIdeal (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField) A)
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (hclosed : p (closedPoint s.residueField) = closedPoint A)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        Function.Surjective sp := by
  intro t hform
  exact surjective_isSpecializationMap_of_isProper_of_flat f s' s hred x' x sp
    (isSpecializationMap_of_isStrictHenselization f s' s A hA p' hp' p hp hclosed x' x sp t hform)

end AlgebraicGeometry

end

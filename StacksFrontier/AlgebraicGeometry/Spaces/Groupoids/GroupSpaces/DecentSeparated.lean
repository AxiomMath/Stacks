module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Separation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Decent groups and groupoids over a field are separated

Let `k` be a field with a morphism `Spec k ⟶ S`. A group algebraic space over `Spec k` which
is decent is a separated algebraic space, and so is the arrow space of a groupoid in algebraic
spaces whose object space is `Spec k` and whose arrow space is decent.

Both statements come from one geometric fact: a section of a morphism from a decent algebraic
space to the algebraic space of a field spectrum is a closed immersion. For a group space that
section is the identity section, and separatedness of the structure morphism is exactly the
identity section being a closed immersion. For a groupoid it is the unit `e : U ⟶ R`, and
separatedness of the target morphism `t : R ⟶ U` follows because the relative diagonal of `t`
is a base change of `e` along the source morphism.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelySeparated_groupAlgebraicSpace_of_isDecentSpace`:
  **Stacks 08BH**, a decent group algebraic space over a field is separated.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isAbsolutelySeparated_arrows_of_isDecentSpace`:
  **Stacks 08BH**, the arrow space of a decent groupoid on a field is separated.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_diagonal_target_identityArrow` and
  `isSeparated_target_of_identityArrow_isClosedImmersion`:
  the relative diagonal of the target morphism of a groupoid in algebraic spaces is a base
  change of its unit, so the target is separated as soon as the unit is a closed immersion.

## Implementation notes

Decency is `AlgebraicGeometry.Space.IsDecentSpace`, which is condition (4) of Stacks 03JV: at
every point there is a field-valued representative presented by a quasi-compact monomorphism.
The section `e` of the statement is itself a monomorphism and represents a point, so Stacks
03E1 identifies it with such a representative; `e` is therefore quasi-compact. On an affine
étale chart `V` of the space the fibre of `e` is then a quasi-compact scheme étale over
`Spec k`, hence has finitely many points and is a finite disjoint union of spectra of finite
separable extensions; in particular it is affine and finite over `Spec k`. Since the fibre maps
to `V` and `V` maps to `Spec k` through the retraction, cancellation of finiteness along the
separated morphism `V ⟶ Spec k` makes the fibre finite over `V`, and a finite monomorphism is a
closed immersion. Being a closed immersion is Zariski local on the target, so the same holds
over an arbitrary étale chart, and fppf descent of closed immersions along the surjective étale
chart finishes the argument; no effective descent is needed because the section is representable
to begin with.

The second assertion of the source is proved through the stabilizer and Stacks 0455. The route
taken here is shorter and gives the same conclusion: the square whose upper edge is the relative
diagonal of `t`, whose left edge is the source morphism, whose lower edge is the unit and whose
right edge sends a pair of arrows with the same target to `b⁻¹ a` is cartesian, because
`b⁻¹ a` is an identity arrow exactly when `a = b`. That is checked on generalized arrows with
the groupoid calculus of Stacks 043W, so no stabilizer is needed.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03E1](https://stacks.math.columbia.edu/tag/03E1)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
* [Stacks Project, Tag 08BH](https://stacks.math.columbia.edu/tag/08BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A scheme with finitely many points which is étale over the spectrum of a field is affine:
it is a disjoint union of spectra of finite separable extensions, and finitely many points
force the index set of that union to be finite. -/
private theorem isAffine_of_finite_of_etale_over_field (k : Type u) [Field k] {W : Scheme.{u}}
    (t : W ⟶ Spec (.of k)) (ht : Etale t) (hW : Finite W) : IsAffine W := by
  obtain ⟨I, K, hfield, halg, -, -, ε, -⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k t).mp ht
  let _ (i : I) : Field (K i) := hfield i
  let _ (i : I) : Algebra k (K i) := halg i
  have hcop : Finite ((∐ fun i ↦ Spec (.of (K i)) : Scheme.{u}) : Type u) :=
    Finite.of_equiv _ (Scheme.homeoOfIso ε).toEquiv
  have hsig : Finite (Σ i : I, (Spec (.of (K i)) : Type u)) :=
    Finite.of_equiv _ (AlgebraicGeometry.sigmaMk fun i ↦ Spec (.of (K i))).toEquiv.symm
  have hne (i : I) : Nonempty (Spec (.of (K i)) : Type u) := inferInstance
  have hI : Finite I :=
    Finite.of_injective
      (fun i ↦ (⟨i, (hne i).some⟩ : Σ i : I, (Spec (.of (K i)) : Type u)))
      fun i j hij ↦ by simpa using congrArg Sigma.fst hij
  have : IsAffine (∐ fun i ↦ Spec (.of (K i))) := inferInstance
  exact IsAffine.of_isIso ε.hom

/-- A morphism split by a retraction stays split after an isomorphism of its source: if
`δ.hom ≫ g = f` and `r` is a retraction of `f`, then `r ≫ δ.hom` is a retraction of `g`.

Stated at an abstract category on purpose: the two sides of the identity reach the same
object through different notations in the application below, and only naming the objects as
variables makes the cancellation a syntactic rewrite. -/
private theorem comp_retraction_eq_id {D : Type*} [Category D] {A B Y : D} (δ : A ≅ B)
    (f : A ⟶ Y) (g : B ⟶ Y) (r : Y ⟶ A) (hδ : δ.hom ≫ g = f) (hr : f ≫ r = 𝟙 A) :
    g ≫ r ≫ δ.hom = 𝟙 B := by
  have hg : g = δ.inv ≫ f := by
    rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
  rw [hg, Category.assoc, ← Category.assoc f r, hr, Category.id_comp, δ.inv_hom_id]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### The algebraic space of an affine scheme is separated -/

/-- The algebraic space of an affine object of the big fppf site of `S` is a separated
algebraic space.

Relocalizing to the terminal scheme carries it to the algebraic space of the image object,
again affine, by Stacks 03I4 (2); the structure morphism of that object to the terminal object
of the site over the terminal scheme is a separated morphism of schemes by Stacks 03KY, and a
space with a separated morphism to a terminal presheaf is separated over its base. -/
private theorem isAbsolutelySeparated_yoneda_of_isAffine (C : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : C.Contains S) (hZ : C.Contains (⊤_ Scheme.{u})) (V : BigFppfOver C S hS)
    (hV : IsAffine ((BigFppfOver.toScheme C S hS).obj V)) :
    IsAbsolutelySeparated C S hS hZ (yoneda.obj V) := by
  have hterm : IsTerminal (Over.mk (𝟙 (C.obj hZ))) := Over.mkIdTerminal
  have hterm' :=
    IsTerminal.isTerminalObj (yoneda (C := BigFppfOver C (⊤_ Scheme.{u}) hZ)) _ hterm
  have haffV : IsAffine ((BigFppfOver.toScheme C (⊤_ Scheme.{u}) hZ).obj
      ((Over.map (⟨terminal.from S⟩ : C.obj hS ⟶ C.obj hZ)).obj V)) := hV
  have haff0 : IsAffine ((BigFppfOver.toScheme C (⊤_ Scheme.{u}) hZ).obj
      (Over.mk (𝟙 (C.obj hZ)))) := inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  have hm : IsSeparated C (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from
      ((Over.map (⟨terminal.from S⟩ : C.obj hS ⟶ C.obj hZ)).obj V))) :=
    isSeparated_yoneda_map_of_isAffine C (⊤_ Scheme.{u}) hZ _ haffV haff0
  have hiso := (OverShriek.relocalizeYonedaIso
    (⟨terminal.from S⟩ : C.obj hS ⟶ C.obj hZ)).app V
  refine (isSeparatedOver_iff_isSeparated_of_isTerminal C (⊤_ Scheme.{u}) hZ hterm'
    (hiso.hom ≫ yoneda.map (hterm.from
      ((Over.map (⟨terminal.from S⟩ : C.obj hS ⟶ C.obj hZ)).obj V)))).2 ?_
  exact isSeparated_comp C (⊤_ Scheme.{u}) hZ _ _
    (isSeparated_of_isIso C (⊤_ Scheme.{u}) hZ hiso.hom) hm

/-! ### A section of a decent algebraic space over a field spectrum -/

/-- The fibre of a quasi-compact monomorphic section over an affine étale chart is a closed
immersion into that chart.

The fibre is étale over the field spectrum because the chart is étale, and quasi-compact
because the chart is affine and the section is quasi-compact; so it has finitely many points
and is affine, hence finite over the field spectrum. The chart maps to the field spectrum
through the retraction, so cancelling the finiteness of the fibre over the field spectrum
against that separated morphism makes the fibre finite over the chart, and a finite
monomorphism of schemes is a closed immersion. -/
private theorem isClosedImmersion_of_isPullback_of_isAffine (C : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : C.Contains S) {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint C S hS X) (hmono : Mono (fieldMorphism C S hS X p))
    (hqc : IsQuasiCompact C S hS (fieldMorphism C S hS X p))
    (r : X ⟶ yoneda.obj p.siteObject)
    (hr : fieldMorphism C S hS X p ≫ r = 𝟙 _) {V W : BigFppfOver C S hS}
    (hV : IsAffine ((BigFppfOver.toScheme C S hS).obj V)) (g : yoneda.obj V ⟶ X)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf g)
    (t : W ⟶ p.siteObject) (n : W ⟶ V)
    (sq : IsPullback (yoneda.map t) (yoneda.map n) (fieldMorphism C S hS X p) g) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme C S hS).map n) := by
  have hetT : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (yoneda.map t) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip hg
  have : Etale ((BigFppfOver.toScheme C S hS).map t) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff C S hS _ t).1 hetT
  have hVcpt : CompactSpace ((BigFppfOver.toScheme C S hS).obj V) := inferInstance
  have hqcs : IsQuasiCompactSpace C S hS (pullback g (fieldMorphism C S hS X p)) :=
    hqc (yoneda.obj V) (isAlgebraicSpace_yoneda C S hS V)
      (isQuasiCompactSpace_yoneda_obj C S hS hVcpt) g
  have hWcpt : CompactSpace ((BigFppfOver.toScheme C S hS).obj W) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj C S hS
      (hqcs.of_iso C S hS
        ((IsPullback.of_hasPullback g (fieldMorphism C S hS X p)).isoIsPullback _ _ sq.flip))
  have hsub : Subsingleton ((BigFppfOver.toScheme C S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hWfin : Finite ((BigFppfOver.toScheme C S hS).obj W) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme C S hS).map t)
  have hWaff : IsAffine ((BigFppfOver.toScheme C S hS).obj W) :=
    isAffine_of_finite_of_etale_over_field p.carrier
      ((BigFppfOver.toScheme C S hS).map t) inferInstance hWfin
  have hfinT : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme C S hS).map t) :=
    isFinite_of_isAffine_of_etale_over_field p.carrier
      ((BigFppfOver.toScheme C S hS).map t)
  obtain ⟨u, hu⟩ : ∃ u : V ⟶ p.siteObject, yoneda.map u = g ≫ r :=
    ⟨yoneda.preimage (g ≫ r), yoneda.map_preimage _⟩
  have hfac : n ≫ u = t := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hu, ← Category.assoc, ← sq.w, Category.assoc, hr, Category.comp_id]
  have : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme C S hS).map u) :=
    inferInstance
  have hfinN : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme C S hS).map n) := by
    have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme C S hS).map n ≫
        (BigFppfOver.toScheme C S hS).map u) := by
      rwa [← Functor.map_comp, hfac]
    exact IsFinite.of_comp _ ((BigFppfOver.toScheme C S hS).map u)
  have : Mono n := yoneda.mono_of_mono_map sq.mono_snd_of_mono
  have : Mono ((BigFppfOver.toScheme C S hS).map n) :=
    Functor.map_mono (BigFppfOver.toScheme C S hS) n
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨hfinN, inferInstance⟩

/-- A quasi-compact monomorphic field-valued point of a decent algebraic space which has a
retraction is a closed immersion.

The fibre over an étale chart is a closed immersion of schemes: being a closed immersion is
Zariski local on the target, so it may be checked over the affine opens of the chart, where
`AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_of_isAffine` applies. The section is
representable because the space has a representable diagonal, so fppf descent of closed
immersions along the surjective étale chart transports the conclusion to the section itself. -/
private theorem isClosedImmersion_fieldMorphism_of_section (C : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : C.Contains S) {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X) (p : FieldValuedPoint C S hS X)
    (hmono : Mono (fieldMorphism C S hS X p))
    (hqc : IsQuasiCompact C S hS (fieldMorphism C S hS X p))
    (r : X ⟶ yoneda.obj p.siteObject)
    (hr : fieldMorphism C S hS X p ≫ r = 𝟙 _) :
    IsClosedImmersion C S hS (fieldMorphism C S hS X p) := by
  have : HasBinaryProducts (BigFppfOver C S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable (fieldMorphism C S hS X p) :=
    (Functor.relativelyRepresentable.diag_iff).1 hX.diagonal_representable _
  obtain ⟨U, a, hasurj, haet⟩ := hX.exists_atlas
  have := isMultiplicative_presheaf_etale C S hS
  have hq : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme C S hS).map (hrep.snd a)) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (fun V : ((BigFppfOver.toScheme C S hS).obj U).affineOpens ↦
        (V : ((BigFppfOver.toScheme C S hS).obj U).Opens))
      (iSup_affineOpens_eq_top _)]
    intro V
    have hVsize : C.Contains (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).toScheme :=
      (Scheme.size_coe_opens_le ((BigFppfOver.toScheme C S hS).obj U) V.1).trans_lt
        U.left.property
    let v : (Over.mk ((ObjectProperty.homMk
        (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).ι :
          C.obj hVsize ⟶ U.left) ≫ U.hom) : BigFppfOver C S hS) ⟶ U :=
      Over.homMk (ObjectProperty.homMk
        (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).ι) rfl
    have hvEt : Etale ((BigFppfOver.toScheme C S hS).map v) := by
      change Etale (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).ι
      infer_instance
    have haV : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (yoneda.map v ≫ a) :=
      MorphismProperty.comp_mem _ _ _
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff C S hS _ v).2 hvEt) haet
    have sqW : IsPullback (yoneda.map (pullback.fst (hrep.snd a) v ≫ hrep.fst' a))
        (yoneda.map (pullback.snd (hrep.snd a) v)) (fieldMorphism C S hS X p)
        (yoneda.map v ≫ a) := by
      simpa only [Functor.map_comp] using
        ((IsPullback.of_hasPullback (hrep.snd a) v).map yoneda).paste_horiz
          (hrep.isPullback' a)
    have hVaff : IsAffine ((BigFppfOver.toScheme C S hS).obj
        (Over.mk ((ObjectProperty.homMk
          (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).ι :
            C.obj hVsize ⟶ U.left) ≫ U.hom) : BigFppfOver C S hS)) := V.2
    have hci := isClosedImmersion_of_isPullback_of_isAffine C S hS p hmono hqc r hr hVaff
      (yoneda.map v ≫ a) haV _ _ sqW
    have sp : IsPullback
        ((BigFppfOver.toScheme C S hS).map (pullback.fst (hrep.snd a) v))
        ((BigFppfOver.toScheme C S hS).map (pullback.snd (hrep.snd a) v))
        ((BigFppfOver.toScheme C S hS).map (hrep.snd a))
        (V : ((BigFppfOver.toScheme C S hS).obj U).Opens).ι :=
      (IsPullback.of_hasPullback (hrep.snd a) v).map (BigFppfOver.toScheme C S hS)
    let j := sp.isoIsPullback _ _
      (isPullback_morphismRestrict
        ((BigFppfOver.toScheme C S hS).map (hrep.snd a)) V.1).flip
    have hj : j.inv ≫ (BigFppfOver.toScheme C S hS).map (pullback.snd (hrep.snd a) v) =
        (BigFppfOver.toScheme C S hS).map (hrep.snd a) ∣_ V.1 := by simp [j]
    have hh := MorphismProperty.RespectsIso.precomp
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) j.inv _ hci
    rwa [hj] at hh
  have hcl : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (yoneda.map (hrep.snd a)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff C S hS _ (hrep.snd a)).2 hq
  have := Stacks.Descent.isClosedImmersion_descendsAlong_fppf.{u}
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong hrep hasurj haet
    (hrep.isPullback' a) hcl

/-- **A section of a decent algebraic space over a field spectrum is a closed immersion.**

The section is a monomorphism, so it presents a point of the space by a monomorphism; decency
provides another monomorphic representative of that point which is in addition quasi-compact,
and Stacks 03E1 identifies the two over the space. The section is therefore a quasi-compact
monomorphism up to an isomorphism of field spectra, which is
`AlgebraicGeometry.Space.isClosedImmersion_fieldMorphism_of_section`.

This is not Stacks 08AL, whose hypotheses are a closed image point and a finite residue
extension rather than a retraction. -/
private theorem isClosedImmersion_section_of_isDecentSpace (C : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : C.Contains S) {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X) (hd : IsDecentSpace C S hS X) (k : Type u) [Field k]
    (hk : C.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    (r : X ⟶ yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)))
    (e : yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)) ⟶ X)
    (he : e ≫ r = 𝟙 _) : IsClosedImmersion C S hS e := by
  have : Mono e := SplitMono.mono ⟨r, he⟩
  let p : FieldValuedPoint C S hS X :=
    { carrier := k, contained := hk, toBase := structureMap, value := yonedaEquiv e }
  have hp : fieldMorphism C S hS X p = e := yonedaEquiv.symm_apply_apply e
  have hmono : Mono (fieldMorphism C S hS X p) := by
    rw [hp]
    infer_instance
  obtain ⟨q, hqclass, hqmono, hqqc⟩ := hd (p.class C S hS X)
  obtain ⟨ε, hε⟩ := iso_of_mono_of_point_eq C S hS X hX p q hqclass.symm
  have hcomp : yoneda.map ε.hom ≫ fieldMorphism C S hS X q = fieldMorphism C S hS X p := by
    apply yonedaEquiv.injective
    simpa only [← yonedaEquiv_naturality, Equiv.apply_symm_apply] using hε
  have he' : fieldMorphism C S hS X p ≫ r = 𝟙 _ := by rwa [hp]
  have hsec : fieldMorphism C S hS X q ≫ (r ≫ yoneda.map ε.hom) = 𝟙 _ :=
    comp_retraction_eq_id (yoneda.mapIso ε) (fieldMorphism C S hS X p)
      (fieldMorphism C S hS X q) r hcomp he'
  have hci := isClosedImmersion_fieldMorphism_of_section C S hS hX q hqmono hqqc _ hsec
  rw [← hp, ← hcomp]
  exact MorphismProperty.RespectsIso.precomp _ (yoneda.map ε.hom) _ hci

/-! ### The group case -/

/-- **Stacks 08BH.** A decent group algebraic space over the spectrum of a field is a separated
algebraic space.

By Stacks 06P6 separatedness of the structure morphism is the identity section being a closed
immersion, and the identity section is a section of the structure morphism, hence a closed
immersion because the space is decent. The base is separated because the spectrum of a field is
affine, so Stacks 04ZH part (1) upgrades separatedness of the structure morphism to
separatedness of the group space. -/
@[stacks 08BH "a decent group algebraic space over a field"]
theorem isAbsolutelySeparated_groupAlgebraicSpace_of_isDecentSpace (k : Type u) [Field k]
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (hZ : C.Contains (⊤_ Scheme.{u}))
    (G : GroupAlgebraicSpace C S hS
      (yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)))
      (isAlgebraicSpace_yoneda C S hS
        (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))))
    (hG : IsDecentSpace C S hS G.obj.X.left) :
    IsAbsolutelySeparated C S hS hZ G.obj.X.left := by
  have hbase : IsAbsolutelySeparated C S hS hZ
      (yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))) :=
    isAbsolutelySeparated_yoneda_of_isAffine C S hS hZ _
      (inferInstanceAs (IsAffine (Spec (.of k))))
  have hsep : IsSeparated C S hS G.obj.X.hom :=
    (isSeparated_iff_identity_isClosedImmersion C S hS _ G).mpr
      (isClosedImmersion_section_of_isDecentSpace C S hS G.property hG k hk structureMap
        G.obj.X.hom (η[G.obj.X]).left (by simp))
  exact isAbsolutelySeparated_of_isSeparated C S hS hZ hbase hsep

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Separatedness of the target morphism of a groupoid -/

/-- For a pair of arrows with the same target, the inverse of the second is composable before
the first. -/
theorem inverseAfterFirst_composable (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pullback.snd G.target.hom G.target.hom ≫ groupoidInverse G) ≫ G.source.hom =
      pullback.fst G.target.hom G.target.hom ≫ G.target.hom := by
  rw [Category.assoc, groupoidInverse_source, pullback.condition]

/-- The generalized arrow `b⁻¹ a` attached to a pair `(a, b)` of arrows with the same target.
It has source the source of `a` and target the source of `b`, and is an identity arrow exactly
when `a = b`. -/
noncomputable def inverseAfterFirst (G : GroupoidInAlgebraicSpaces C S hS B) :
    pullback G.target.hom G.target.hom ⟶ G.arrows.obj :=
  groupoidCompose G
    (pullback.snd G.target.hom G.target.hom ≫ groupoidInverse G)
    (pullback.fst G.target.hom G.target.hom)
    (inverseAfterFirst_composable G)

/-- A pair of generalized arrows with the same target whose composite `b⁻¹ a` is an identity
arrow is a pair of equal arrows, and that arrow has the source of the identity.

Composing `b` after `b⁻¹ a` gives `a` by the inverse and unit laws, and gives `b` because
`b⁻¹ a` is the identity at the source of `b`. -/
private theorem eq_of_groupoidCompose_inverse_eq_identityArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a b : T ⟶ G.arrows.obj)
    (w : (b ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom)
    (y : T ⟶ G.objects.obj)
    (hy : groupoidCompose G (b ≫ groupoidInverse G) a w = y ≫ (identityArrow G).hom) :
    a = b ∧ a ≫ G.source.hom = y := by
  have hinv : (b ≫ groupoidInverse G) ≫ G.target.hom = b ≫ G.source.hom := by
    rw [Category.assoc, groupoidInverse_target]
  have hsrc : a ≫ G.source.hom = y := by
    have h1 := groupoidCompose_source G (b ≫ groupoidInverse G) a w
    rw [hy] at h1
    rw [← h1, Category.assoc, identityArrow_hom_comp_source, Category.comp_id]
  have htgt : b ≫ G.source.hom = y := by
    have h1 := groupoidCompose_target G (b ≫ groupoidInverse G) a w
    rw [hy, hinv] at h1
    rw [← h1, Category.assoc, identityArrow_hom_comp_target, Category.comp_id]
  have hab : a ≫ G.target.hom = b ≫ G.target.hom := by
    rw [← w, Category.assoc, groupoidInverse_source]
  refine ⟨?_, hsrc⟩
  have wab : b ≫ G.source.hom = (b ≫ groupoidInverse G) ≫ G.target.hom := hinv.symm
  have wL : groupoidCompose G b (b ≫ groupoidInverse G) wab ≫ G.source.hom =
      a ≫ G.target.hom := by
    rwa [groupoidCompose_source]
  have wR : b ≫ G.source.hom =
      groupoidCompose G (b ≫ groupoidInverse G) a w ≫ G.target.hom := by
    rw [groupoidCompose_target, hinv]
  have hassoc := groupoidCompose_assoc G b (b ≫ groupoidInverse G) a wab w wL wR
  have hidb : groupoidCompose G b (b ≫ groupoidInverse G) wab = identityAfterTarget G a := by
    refine (groupoidCompose_inverseLeft G b).trans ?_
    rw [identityAfterTarget, identityAfterTarget, ← Category.assoc, ← Category.assoc, hab]
  have hleft : groupoidCompose G (groupoidCompose G b (b ≫ groupoidInverse G) wab) a wL = a :=
    (groupoidCompose_congr G wL _ hidb rfl).trans (groupoidCompose_leftIdentity G a)
  have hida : groupoidCompose G (b ≫ groupoidInverse G) a w = identityAfterSource G b := by
    rw [hy, identityAfterSource, ← Category.assoc, htgt]
  have hright : groupoidCompose G b (groupoidCompose G (b ≫ groupoidInverse G) a w) wR = b :=
    (groupoidCompose_congr G wR _ rfl hida).trans (groupoidCompose_rightIdentity G b)
  exact hleft.symm.trans (hassoc.trans hright)

/-- **The relative diagonal of the target morphism of a groupoid in algebraic spaces is a base
change of its unit.** The square whose upper edge is the relative diagonal of the target, whose
left edge is the source, whose lower edge is the unit and whose right edge sends a pair `(a, b)`
of arrows with the same target to `b⁻¹ a` is cartesian.

It commutes because `a⁻¹ a` is the identity at the source of `a`, and it is cartesian because
`b⁻¹ a` is an identity arrow exactly when `a = b`. -/
theorem isPullback_diagonal_target_identityArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback (pullback.diagonal G.target.hom) G.source.hom (inverseAfterFirst G)
      (identityArrow G).hom := by
  have hw : pullback.diagonal G.target.hom ≫ inverseAfterFirst G =
      G.source.hom ≫ (identityArrow G).hom := by
    have h1 : pullback.diagonal G.target.hom ≫
        (pullback.snd G.target.hom G.target.hom ≫ groupoidInverse G) =
        𝟙 G.arrows.obj ≫ groupoidInverse G := by
      rw [← Category.assoc, pullback.diagonal_snd]
    have w' : (𝟙 G.arrows.obj ≫ groupoidInverse G) ≫ G.source.hom =
        𝟙 G.arrows.obj ≫ G.target.hom := by
      rw [Category.assoc, groupoidInverse_source]
    rw [inverseAfterFirst, groupoidCompose_pre]
    refine (groupoidCompose_congr G _ w' h1 (pullback.diagonal_fst _)).trans ?_
    refine (groupoidCompose_inverseRight G (𝟙 G.arrows.obj)).trans ?_
    rw [identityAfterSource, Category.id_comp]
  have key : ∀ {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
      (x : T ⟶ pullback G.target.hom G.target.hom) (y : T ⟶ G.objects.obj),
      x ≫ inverseAfterFirst G = y ≫ (identityArrow G).hom →
      x ≫ pullback.fst G.target.hom G.target.hom =
          x ≫ pullback.snd G.target.hom G.target.hom ∧
        (x ≫ pullback.fst G.target.hom G.target.hom) ≫ G.source.hom = y := by
    intro T x y hxy
    have w : ((x ≫ pullback.snd G.target.hom G.target.hom) ≫ groupoidInverse G) ≫
        G.source.hom = (x ≫ pullback.fst G.target.hom G.target.hom) ≫ G.target.hom := by
      rw [Category.assoc, groupoidInverse_source, Category.assoc, Category.assoc,
        pullback.condition]
    have hx : x ≫ inverseAfterFirst G =
        groupoidCompose G ((x ≫ pullback.snd G.target.hom G.target.hom) ≫ groupoidInverse G)
          (x ≫ pullback.fst G.target.hom G.target.hom) w := by
      rw [inverseAfterFirst, groupoidCompose_pre]
      exact groupoidCompose_congr G _ _ (Category.assoc _ _ _).symm rfl
    exact eq_of_groupoidCompose_inverse_eq_identityArrow G _ _ w y (hx.symm.trans hxy)
  refine { w := hw, isLimit' := ⟨?_⟩ }
  refine PullbackCone.IsLimit.mk hw
    (lift := fun c ↦ c.fst ≫ pullback.fst G.target.hom G.target.hom) ?_ ?_ ?_
  · intro c
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (key c.fst c.snd c.condition).1
  · intro c
    exact (key c.fst c.snd c.condition).2
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **The target morphism of a groupoid in algebraic spaces whose unit is a closed immersion is
separated.** Its relative diagonal is a base change of the unit, and being a closed immersion is
a relative property of morphisms of presheaves, hence stable under base change. -/
theorem isSeparated_target_of_identityArrow_isClosedImmersion
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (he : Space.IsClosedImmersion C S hS (identityArrow G).hom) :
    Space.IsSeparated C S hS G.target.hom :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS))).of_isPullback
    (isPullback_diagonal_target_identityArrow G).flip he

/-! ### The groupoid case -/

/-- **Stacks 08BH.** The arrow space of a groupoid in algebraic spaces whose object space is
the algebraic space of the spectrum of a field and whose arrow space is decent is a separated
algebraic space.

The unit of the groupoid is a section of the source morphism, hence a closed immersion because
the arrow space is decent; the target morphism is then separated, and the object space is
separated because the spectrum of a field is affine, so Stacks 04ZH part (1) applies. -/
@[stacks 08BH "the arrows of a decent groupoid on a field"]
theorem isAbsolutelySeparated_arrows_of_isDecentSpace (k : Type u) [Field k]
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (hZ : C.Contains (⊤_ Scheme.{u})) (B : AlgebraicSpaces C S hS)
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)))
    (hR : Space.IsDecentSpace C S hS G.arrows.obj) :
    Space.IsAbsolutelySeparated C S hS hZ G.arrows.obj := by
  let i : G.objects.obj ≅
      yoneda.obj (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)) := eqToIso hU
  have hsec : (i.inv ≫ (identityArrow G).hom) ≫ (G.source.hom ≫ i.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc ((identityArrow G).hom),
      identityArrow_hom_comp_source, Category.id_comp, i.inv_hom_id]
  have hunit : Space.IsClosedImmersion C S hS (identityArrow G).hom := by
    have h := Space.isClosedImmersion_section_of_isDecentSpace C S hS G.arrows.property hR
      k hk structureMap (G.source.hom ≫ i.hom) (i.inv ≫ (identityArrow G).hom) hsec
    have h2 := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf i.hom _ h
    rwa [← Category.assoc, i.hom_inv_id, Category.id_comp] at h2
  refine Space.isAbsolutelySeparated_of_isSeparated C S hS hZ ?_
    (isSeparated_target_of_identityArrow_isClosedImmersion G hunit)
  rw [hU]
  exact Space.isAbsolutelySeparated_yoneda_of_isAffine C S hS hZ _
    (inferInstanceAs (IsAffine (Spec (.of k))))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRelativeDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceGeneralCase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison

/-!
# The spaces-étale sites over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `Z` an algebraic space over `W`, `Y` one over
`S` and `ε : Λ_h Z ≅ Y`. The lower-shriek extension carries algebraic spaces étale over `Z` to
algebraic spaces étale over `Y` (`AlgebraicGeometry.Space.isEtale_relocalize_iff`). This file
builds that functor of spaces-étale sites (Stacks 03G0), the first step of the comparison of the
direct images of an arbitrary morphism over the two bases
(`AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison`).

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseSpacesEtaleFunctor`: the functor
  `Z_{spaces,étale} ⥤ Y_{spaces,étale}`, `T ↦ Λ_h T`.
* `AlgebraicGeometry.Space.smallerBaseSpacesEtaleEquivalence`: it is an equivalence.

## Main results

* `AlgebraicGeometry.Space.exists_relocalizePresheafFunctor_map_eq`: `Λ_h` is full over `h_W`.
* `AlgebraicGeometry.Space.smallerBaseSpacesEtaleFunctor_faithful`,
  `AlgebraicGeometry.Space.smallerBaseSpacesEtaleFunctor_full` and
  `AlgebraicGeometry.Space.smallerBaseSpacesEtaleFunctor_essSurj`: it is fully faithful and
  essentially surjective (Stacks 04SG).
* `AlgebraicGeometry.Space.smallerBaseSpacesEtaleFunctor_isContinuous`: it is continuous for the
  spaces-étale topologies.
* `AlgebraicGeometry.Space.smallerBaseComparisonIso`: it extends the equivalence of small étale
  sites `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso` along the comparison
  functors of Stacks 03G1.
* `AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeIso`: it commutes with the base-change
  functors `AlgebraicGeometry.Space.spacesBaseChange` of Stacks 03G2, compatibly with the cartesian
  projections (`AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeObjIso_hom_projection`).
* `AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso`: the small étale direct images of
  sheaves of sets of an arbitrary morphism commute with the change of base.

## The rest of `AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison`

The comparison of the structure maps and of the direct images of modules is in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseStructureSharp.lean`, and the derived form in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseDerivedPushforward.lean`.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)

/-- An algebraic space étale over `Z`, viewed over `Y` through `Λ_h` and `ε`. -/
abbrev smallerBaseSpacesEtaleObj (T : SpacesEtale B W hW Z) : SpacesEtale B S hS Y :=
  ⟨Over.mk (ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor h).map T.1.hom.hom ≫
      ε.hom) : relocalizeSpace B hW hS h T.1.left ⟶ Y),
    isEtale_comp B S hS
      ((isEtale_relocalize_iff B W S hW hS h T.1.left.2 Z.2 T.1.hom.hom).2 T.2)
      (isEtale_of_isIso B S hS ε.hom)⟩

/-- **The spaces-étale site of `Z` maps to that of `Y`**: an algebraic space `T` étale over `Z`
goes to `Λ_h T`, étale over `Λ_h Z ≅ Y`. -/
def smallerBaseSpacesEtaleFunctor : SpacesEtale B W hW Z ⥤ SpacesEtale B S hS Y where
  obj T := smallerBaseSpacesEtaleObj B h ε T
  map {T T'} a := ObjectProperty.homMk (Over.homMk (relocalizeSpaceMap h a.hom.left) (by
    apply ObjectProperty.hom_ext
    change (OverShriek.relocalizePresheafFunctor h).map a.hom.left.hom ≫
        (OverShriek.relocalizePresheafFunctor h).map T'.1.hom.hom ≫ ε.hom =
      (OverShriek.relocalizePresheafFunctor h).map T.1.hom.hom ≫ ε.hom
    rw [← Functor.map_comp_assoc]
    exact congrArg (fun k => (OverShriek.relocalizePresheafFunctor h).map k ≫ ε.hom)
      (congrArg (fun k => k.hom) (Over.w a.hom))))
  map_id T := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (OverShriek.relocalizePresheafFunctor h).map_id _
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (OverShriek.relocalizePresheafFunctor h).map_comp _ _

/-- The functor of spaces-étale sites is faithful, `Λ_h` being faithful. -/
instance smallerBaseSpacesEtaleFunctor_faithful :
    (smallerBaseSpacesEtaleFunctor B h ε).Faithful where
  map_injective {T T'} a b e := by
    have _ := relocalizePresheaf_faithful h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (OverShriek.relocalizePresheafFunctor h).map_injective
      (congrArg (fun k => k.hom.left.hom) e)

section Full

variable {B h}

/-- The structural morphism of the image of a presheaf under the equivalence of Stacks 04SG is the
structural morphism `AlgebraicGeometry.OverShriek.relocalizeToYoneda` of its lower-shriek
extension, read through `AlgebraicGeometry.smallerBasePresheafForgetIso`. -/
theorem smallerBasePresheafEquivalence_obj_hom (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    ((smallerBasePresheafEquivalence B W S hW hS h).functor.obj F).hom =
      (smallerBasePresheafForgetIso B W S hW hS h).hom.app F ≫
        OverShriek.relocalizeToYoneda h F := by
  ext T x
  exact Over.OverMorphism.ext rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **`Λ_h` is full over `h_W`**: a morphism `Λ_h F ⟶ Λ_h G` of presheaves over `S` compatible with
the structural morphisms to the representable presheaf of `h` is `Λ_h` of a morphism `F ⟶ G`. This
is the fullness of the equivalence of Stacks 04SG on presheaves. -/
theorem exists_relocalizePresheafFunctor_map_eq {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (φ : (OverShriek.relocalizePresheafFunctor h).obj F ⟶
      (OverShriek.relocalizePresheafFunctor h).obj G)
    (hφ : φ ≫ OverShriek.relocalizeToYoneda h G = OverShriek.relocalizeToYoneda h F) :
    ∃ k : F ⟶ G, (OverShriek.relocalizePresheafFunctor h).map k = φ := by
  let E := smallerBasePresheafEquivalence B W S hW hS h
  let c := smallerBasePresheafForgetIso B W S hW hS h
  let ψ : E.functor.obj F ⟶ E.functor.obj G :=
    Over.homMk (c.hom.app F ≫ φ ≫ c.inv.app G) (by
      rw [smallerBasePresheafEquivalence_obj_hom, smallerBasePresheafEquivalence_obj_hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, hφ])
  refine ⟨E.functor.preimage ψ, ?_⟩
  have hn := c.hom.naturality (E.functor.preimage ψ)
  rw [Functor.comp_map, Functor.map_preimage] at hn
  rw [show (Over.forget _).map ψ = c.hom.app F ≫ φ ≫ c.inv.app G from rfl] at hn
  simpa using (c.inv.app F ≫= hn).symm

variable (B h) in
/-- The functor of spaces-étale sites is full, by the fullness of `Λ_h` over `h_W`
(`AlgebraicGeometry.Space.exists_relocalizePresheafFunctor_map_eq`). -/
instance smallerBaseSpacesEtaleFunctor_full : (smallerBaseSpacesEtaleFunctor B h ε).Full where
  map_surjective {T T'} φ := by
    have _ := relocalizePresheaf_faithful h
    let Λ := OverShriek.relocalizePresheafFunctor h
    have hw : φ.hom.left.hom ≫ Λ.map T'.1.hom.hom ≫ ε.hom = Λ.map T.1.hom.hom ≫ ε.hom :=
      congrArg (fun k => k.hom) (Over.w φ.hom)
    have hw' : φ.hom.left.hom ≫ Λ.map T'.1.hom.hom = Λ.map T.1.hom.hom := by
      exact (Iso.cancel_iso_hom_right _ _ ε).1 ((Category.assoc _ _ _).trans hw)
    have hφ : φ.hom.left.hom ≫ OverShriek.relocalizeToYoneda h T'.1.left.1 =
        OverShriek.relocalizeToYoneda h T.1.left.1 := by
      exact (congrArg (φ.hom.left.hom ≫ ·)
        (relocalizeToYoneda_naturality B W S hW hS h T'.1.hom.hom).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ OverShriek.relocalizeToYoneda h Z.1) hw').trans
            (relocalizeToYoneda_naturality B W S hW hS h T.1.hom.hom)))
    obtain ⟨k, hk⟩ := exists_relocalizePresheafFunctor_map_eq φ.hom.left.hom hφ
    have hkw : k ≫ T'.1.hom.hom = T.1.hom.hom :=
      Λ.map_injective (by rw [Λ.map_comp, hk]; exact hw')
    refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk k)
      (ObjectProperty.hom_ext _ hkw)), ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact ObjectProperty.hom_ext _ hk

variable (B h) in
/-- The functor of spaces-étale sites is essentially surjective: an algebraic space `T'` étale over
`Y` is, by Stacks 04SG, `Λ_h` of an algebraic space over `W`, whose morphism to `Z` comes from the
fullness of `Λ_h` over `h_W` and is étale by `AlgebraicGeometry.Space.isEtale_relocalize_iff`. -/
instance smallerBaseSpacesEtaleFunctor_essSurj : (smallerBaseSpacesEtaleFunctor B h ε).EssSurj where
  mem_essImage T' := by
    have _ := relocalizePresheaf_faithful h
    let Λ := OverShriek.relocalizePresheafFunctor h
    let E := smallerBasePresheafEquivalence B W S hW hS h
    let c := smallerBasePresheafForgetIso B W S hW hS h
    let q : T'.1.left.1 ⟶ yoneda.obj (Over.mk h) :=
      T'.1.hom.hom ≫ ε.inv ≫ OverShriek.relocalizeToYoneda h Z.1
    let O : Over (yoneda.obj (Over.mk h)) := Over.mk q
    let F₀ := E.inverse.obj O
    have hF₀ : IsAlgebraicSpace B W hW F₀ :=
      isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B W S hW hS h O T'.1.left.2
    let θ : Λ.obj F₀ ≅ T'.1.left.1 := (c.app F₀).symm ≪≫ (Over.forget _).mapIso (E.counitIso.app O)
    have hθ : θ.hom ≫ q = OverShriek.relocalizeToYoneda h F₀ := by
      have hw := Over.w (E.counitIso.app O).hom
      have h₀ := smallerBasePresheafEquivalence_obj_hom (h := h) F₀
      change (c.app F₀).inv ≫ (E.counitIso.app O).hom.left ≫ q = _
      refine (congrArg ((c.app F₀).inv ≫ ·) hw).trans ?_
      change (c.app F₀).inv ≫ (E.functor.obj F₀).hom = _
      rw [h₀]
      exact (c.app F₀).inv_hom_id_assoc _
    let φ : Λ.obj F₀ ⟶ Λ.obj Z.1 := θ.hom ≫ T'.1.hom.hom ≫ ε.inv
    have hφ : φ ≫ OverShriek.relocalizeToYoneda h Z.1 = OverShriek.relocalizeToYoneda h F₀ := by
      rw [← hθ]
      simp only [φ, q, Category.assoc]
    obtain ⟨k, hk⟩ := exists_relocalizePresheafFunctor_map_eq φ hφ
    have hket : IsEtale B W hW k := by
      refine (isEtale_relocalize_iff B W S hW hS h hF₀ Z.2 k).1 ?_
      rw [hk]
      change IsEtale B S hS (θ.hom ≫ T'.1.hom.hom ≫ ε.inv)
      exact isEtale_comp B S hS (isEtale_of_isIso B S hS θ.hom)
        (isEtale_comp B S hS T'.2 (isEtale_of_isIso B S hS ε.inv))
    let T₀ : SpacesEtale B W hW Z :=
      ⟨Over.mk (ObjectProperty.homMk k : (⟨F₀, hF₀⟩ : AlgebraicSpaces B W hW) ⟶ Z), hket⟩
    refine ⟨T₀, ⟨ObjectProperty.isoMk _ (Over.isoMk (ObjectProperty.isoMk _ θ) ?_)⟩⟩
    apply ObjectProperty.hom_ext
    change θ.hom ≫ T'.1.hom.hom = Λ.map k ≫ ε.hom
    rw [hk]
    simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The equivalence of spaces-étale sites and its continuity -/

variable (B h) in
/-- The functor of spaces-étale sites is an equivalence: it is fully faithful and essentially
surjective. -/
instance smallerBaseSpacesEtaleFunctor_isEquivalence :
    (smallerBaseSpacesEtaleFunctor B h ε).IsEquivalence where

variable (B h) in
/-- **The spaces-étale sites of `Z` and of `Y` are equivalent** when `Λ_h Z ≅ Y` (Stacks 04SG). -/
def smallerBaseSpacesEtaleEquivalence : SpacesEtale B W hW Z ≌ SpacesEtale B S hS Y :=
  (smallerBaseSpacesEtaleFunctor B h ε).asEquivalence

variable (B h) in
/-- The functor of spaces-étale sites is continuous: it carries a jointly point-surjective
family to one, the points of `T` and of `Λ_h T` corresponding naturally
(`AlgebraicGeometry.Space.pointsRelocalize_bijective`). -/
instance smallerBaseSpacesEtaleFunctor_isContinuous :
    (smallerBaseSpacesEtaleFunctor B h ε).IsContinuous (SpacesEtale.topology B W hW Z)
      (SpacesEtale.topology B S hS Y) := by
  let e := smallerBaseSpacesEtaleEquivalence B h ε
  change e.functor.IsContinuous _ _
  apply Functor.le_inducedTopology_iff.mp
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro U R hR
  obtain ⟨E, rfl, hE⟩ := hR
  change Sieve.generate E.presieve₀ ∈ e.functor.inducedTopology _ U
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, ← Sieve.generate_map_eq_functorPushforward,
    ← PreZeroHypercover.presieve₀_map]
  refine Precoverage.generate_mem_toGrothendieck ⟨E.map e.functor, rfl, fun x' => ?_⟩
  obtain ⟨x, rfl⟩ := pointsRelocalize_surjective B W S hW hS h U.1.left.1 x'
  obtain ⟨i, y, hy⟩ := hE x
  exact ⟨i, pointsRelocalize B W S hW hS h _ y,
    (pointsRelocalize_naturality B W S hW hS h (E.f i).hom.left.hom y).symm.trans
      (congrArg (pointsRelocalize B W S hW hS h U.1.left.1) hy)⟩

/-! ### Compatibility with the comparison functors of Stacks 03G1 -/

variable (B h) in
/-- **The equivalence of spaces-étale sites extends that of small étale sites**: viewing a scheme
chart of `Z` as an algebraic space étale over `Z` and then over `Y` is viewing it as a chart of
`Y` and then as an algebraic space étale over `Y`, through the identification
`Λ_h h_U ≅ h_{Over.map h U}` of Stacks 03I4 (2) (`AlgebraicGeometry.relocalizedYonedaIso`). -/
def smallerBaseComparisonIso :
    comparisonFunctor B W hW Z ⋙ smallerBaseSpacesEtaleFunctor B h ε ≅
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor ⋙ comparisonFunctor B S hS Y :=
  NatIso.ofComponents (fun U => ObjectProperty.isoMk _ (Over.isoMk (ObjectProperty.isoMk _
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U.1.left)) (by
      apply ObjectProperty.hom_ext
      change (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U.1.left).hom ≫
          (relocalizeChart B W S hW hS h U.1.hom ≫ ε.hom) =
        (OverShriek.relocalizePresheafFunctor h).map U.1.hom ≫ ε.hom
      rw [relocalizeChart, Category.assoc, Iso.hom_inv_id_assoc])))
    (fun {U U'} k => by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h k.hom.left)

end Full

/-! ### Compatibility with base change -/

section BaseChange

variable {B h} in
/-- `AlgebraicGeometry.Space.relocalizeSpaceMap` preserves composition. -/
theorem relocalizeSpaceMap_comp {X X' X'' : AlgebraicSpaces B W hW} (a : X ⟶ X') (b : X' ⟶ X'') :
    relocalizeSpaceMap h (a ≫ b) = relocalizeSpaceMap h a ≫ relocalizeSpaceMap h b :=
  ObjectProperty.hom_ext _ ((OverShriek.relocalizePresheafFunctor h).map_comp _ _)

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)

include hfg in
/-- **The extension of a base change is a base change**: for `V` étale over `Z₂`, the extension
along `h` of the base change of `V` along `f` is a fibre product of `g` and of the extension of
`V`, read through `ε₁` and `ε₂`, the lower-shriek extension preserving fibre products. -/
theorem isPullback_smallerBaseSpacesEtale_spacesBaseChange (V : SpacesEtale B W hW Z₂) :
    IsPullback (relocalizeSpaceMap h ((spacesBaseChange B W hW f).projection.app V))
      ((smallerBaseSpacesEtaleFunctor B h ε₁).obj ((spacesBaseChange B W hW f).functor.obj V)).1.hom
      ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V).1.hom g := by
  have := relocalizePresheaf_preservesConnectedLimits (K := WalkingCospan) h
  have h₁ := (OverShriek.relocalizePresheafFunctor h).map_isPullback
    (AlgebraicSpaces.isPullback_hom B W hW ((spacesBaseChange B W hW f).isPullback V))
  have h₂ : IsPullback
      ((OverShriek.relocalizePresheafFunctor h).map
        ((spacesBaseChange B W hW f).projection.app V).hom)
      ((OverShriek.relocalizePresheafFunctor h).map
        ((spacesBaseChange B W hW f).functor.obj V).1.hom.hom ≫ ε₁.hom)
      ((OverShriek.relocalizePresheafFunctor h).map V.1.hom.hom ≫ ε₂.hom) g.hom :=
    h₁.of_iso (Iso.refl _) (Iso.refl _) ε₁ ε₂ (by simp) (by simp) (by simp) hfg.symm
  refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h₂.w) h₂

/-- The comparison of the extension of a base change along `f` with the base change along `g` of
the extension, on one object of the spaces-étale site of `Z₂`. -/
def smallerBaseSpacesBaseChangeObjIso (V : SpacesEtale B W hW Z₂) :
    (smallerBaseSpacesEtaleFunctor B h ε₁).obj ((spacesBaseChange B W hW f).functor.obj V) ≅
      (spacesBaseChange B S hS g).functor.obj ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V) :=
  ObjectProperty.isoMk _ (Over.isoMk
    ((isPullback_smallerBaseSpacesEtale_spacesBaseChange B h ε₁ ε₂ hfg V).isoIsPullback _ _
      ((spacesBaseChange B S hS g).isPullback _))
    (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- The comparison `AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeObjIso` is compatible with
the cartesian projections: it carries the projection of the base change along `g` to the extension
of the projection of the base change along `f`. -/
@[reassoc]
theorem smallerBaseSpacesBaseChangeObjIso_hom_projection (V : SpacesEtale B W hW Z₂) :
    (smallerBaseSpacesBaseChangeObjIso B h ε₁ ε₂ hfg V).hom.hom.left ≫
        (spacesBaseChange B S hS g).projection.app ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V) =
      relocalizeSpaceMap h ((spacesBaseChange B W hW f).projection.app V) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **Base change commutes with the change of base on spaces-étale sites**: extending along `h`
and then base changing along `g` is base changing along `f` and then extending. The components
are pinned down by their compatibility with the cartesian projections
(`AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeObjIso_hom_projection`). -/
def smallerBaseSpacesBaseChangeIso :
    (spacesBaseChange B W hW f).functor ⋙ smallerBaseSpacesEtaleFunctor B h ε₁ ≅
      smallerBaseSpacesEtaleFunctor B h ε₂ ⋙ (spacesBaseChange B S hS g).functor :=
  NatIso.ofComponents (smallerBaseSpacesBaseChangeObjIso B h ε₁ ε₂ hfg) fun {V V'} k => by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ((spacesBaseChange B S hS g).isPullback
      ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V')).hom_ext
    · have n₁ : ((spacesBaseChange B W hW f).functor.map k).hom.left ≫
          (spacesBaseChange B W hW f).projection.app V' =
          (spacesBaseChange B W hW f).projection.app V ≫ k.hom.left :=
        (spacesBaseChange B W hW f).projection.naturality k
      have n₂ : ((spacesBaseChange B S hS g).functor.map
            ((smallerBaseSpacesEtaleFunctor B h ε₂).map k)).hom.left ≫
          (spacesBaseChange B S hS g).projection.app
              ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V') =
          (spacesBaseChange B S hS g).projection.app
              ((smallerBaseSpacesEtaleFunctor B h ε₂).obj V) ≫
            relocalizeSpaceMap h k.hom.left :=
        (spacesBaseChange B S hS g).projection.naturality _
      have r : relocalizeSpaceMap h ((spacesBaseChange B W hW f).functor.map k).hom.left ≫
          relocalizeSpaceMap h ((spacesBaseChange B W hW f).projection.app V') =
          relocalizeSpaceMap h ((spacesBaseChange B W hW f).projection.app V) ≫
            relocalizeSpaceMap h k.hom.left := by
        rw [← relocalizeSpaceMap_comp, ← relocalizeSpaceMap_comp, n₁]
      have p₁ := smallerBaseSpacesBaseChangeObjIso_hom_projection B h ε₁ ε₂ hfg V
      have p₂ := smallerBaseSpacesBaseChangeObjIso_hom_projection B h ε₁ ε₂ hfg V'
      exact (congrArg
        (relocalizeSpaceMap h ((spacesBaseChange B W hW f).functor.map k).hom.left ≫ ·)
        p₂).trans (r.trans ((p₁ =≫ relocalizeSpaceMap h k.hom.left).symm.trans
          ((Category.assoc _ _ _).trans (congrArg
            ((smallerBaseSpacesBaseChangeObjIso B h ε₁ ε₂ hfg V).hom.hom.left ≫ ·) n₂.symm))))
    · exact (Over.w ((((spacesBaseChange B W hW f).functor ⋙
            smallerBaseSpacesEtaleFunctor B h ε₁).map k ≫
          (smallerBaseSpacesBaseChangeObjIso B h ε₁ ε₂ hfg V').hom).hom)).trans
        (Over.w ((smallerBaseSpacesBaseChangeObjIso B h ε₁ ε₂ hfg V).hom ≫
          (smallerBaseSpacesEtaleFunctor B h ε₂ ⋙
            (spacesBaseChange B S hS g).functor).map k).hom).symm

end BaseChange

/-! ### The direct images of sheaves of sets -/

section SheafPushforward

/-- **The change of base on spaces-étale sheaves is the change of base on small étale sheaves**,
through the comparison equivalences of Stacks 03G1: restricting along `Φ` and then to charts of
`Z` is restricting to charts of `Y` and then along the equivalence of small étale sites. This is
`AlgebraicGeometry.Space.smallerBaseComparisonIso` on sheaves. -/
def smallerBaseComparisonRestrictionIso :
    (smallerBaseSpacesEtaleFunctor B h ε).sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z) (SpacesEtale.topology B S hS Y) ⋙
      smallEtaleComparisonRestriction B W hW Z ≅
    smallEtaleComparisonRestriction B S hS Y ⋙
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS Y.1) :=
  haveI := Functor.isContinuous_comp (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
    (comparisonFunctor B S hS Y) (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y)
  Functor.sheafPushforwardContinuousComp' (smallerBaseComparisonIso B h ε) (Type u) _
    (SpacesEtale.topology B W hW Z) _ ≪≫
  (Functor.sheafPushforwardContinuousComp _ _ (Type u) _ (SmallEtale.topology B S hS Y.1) _).symm

/-- The inverse comparison equivalences of Stacks 03G1 intertwine the two changes of base on
sheaves: `AlgebraicGeometry.Space.smallerBaseComparisonRestrictionIso` conjugated by the
comparison equivalences. -/
def smallerBaseComparisonRestrictionInverseIso :
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
      (smallerBaseSpacesEtaleFunctor B h ε).sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z) (SpacesEtale.topology B S hS Y) ≅
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS Y.1) ⋙
      (smallEtaleComparisonRestriction B W hW Z).asEquivalence.inverse :=
  Iso.inverseCompIso (G := (smallEtaleComparisonRestriction B S hS Y).asEquivalence)
    (Iso.isoCompInverse (H := (smallEtaleComparisonRestriction B W hW Z).asEquivalence)
      (smallerBaseComparisonRestrictionIso B h ε))

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)

/-- **The spaces-étale direct images commute with the change of base**: restriction along
`spacesBaseChange g` then along `Φ₂` is restriction along `Φ₁` then along `spacesBaseChange f`.
This is `AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeIso` on sheaves. -/
def smallerBaseSpacesPushforwardIso :
    (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y₂) (SpacesEtale.topology B S hS Y₁) ⋙
      (smallerBaseSpacesEtaleFunctor B h ε₂).sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z₂) (SpacesEtale.topology B S hS Y₂) ≅
    (smallerBaseSpacesEtaleFunctor B h ε₁).sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z₁) (SpacesEtale.topology B S hS Y₁) ⋙
      (spacesBaseChange B W hW f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z₂) (SpacesEtale.topology B W hW Z₁) :=
  haveI := Functor.isContinuous_comp (spacesBaseChange B W hW f).functor
    (smallerBaseSpacesEtaleFunctor B h ε₁) (SpacesEtale.topology B W hW Z₂)
    (SpacesEtale.topology B W hW Z₁) (SpacesEtale.topology B S hS Y₁)
  Functor.sheafPushforwardContinuousComp' (smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).symm
    (Type u) _ (SpacesEtale.topology B S hS Y₂) _ ≪≫
  (Functor.sheafPushforwardContinuousComp _ _ (Type u) _ (SpacesEtale.topology B W hW Z₁) _).symm

/-- **The direct images of sheaves of sets commute with the change of base**, for an arbitrary
morphism: `g_* ⋙ (−)' ≅ (−)' ⋙ f_*` for the small étale direct images
`AlgebraicGeometry.Space.smallEtaleDirectImage` of `g` and of `f`, the change of base `(−)'` being
restriction along the equivalences of small étale sites
`AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`. Both direct images are
spaces-étale direct images conjugated by the comparison equivalences of Stacks 03G1, and these
commute with the change of base by `AlgebraicGeometry.Space.smallerBaseComparisonRestrictionIso`
and `AlgebraicGeometry.Space.smallerBaseSpacesPushforwardIso`. -/
def smallerBaseSmallEtaleDirectImageIso :
    smallEtaleDirectImage B S hS g ⋙
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1) ≅
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1) ⋙
      smallEtaleDirectImage B W hW f :=
  Functor.isoWhiskerLeft ((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse ⋙
      (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y₂) (SpacesEtale.topology B S hS Y₁))
    (smallerBaseComparisonRestrictionIso B h ε₂).symm ≪≫
  Functor.isoWhiskerLeft (smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse
    (Functor.isoWhiskerRight (smallerBaseSpacesPushforwardIso B h ε₁ ε₂ hfg)
      (smallEtaleComparisonRestriction B W hW Z₂)) ≪≫
  Functor.isoWhiskerRight (smallerBaseComparisonRestrictionInverseIso B h ε₁)
    ((spacesBaseChange B W hW f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z₂) (SpacesEtale.topology B W hW Z₁) ⋙
      smallEtaleComparisonRestriction B W hW Z₂)

end SheafPushforward

end AlgebraicGeometry.Space

end

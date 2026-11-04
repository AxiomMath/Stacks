module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingPropertyTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
import StacksFrontier.AlgebraicGeometry.Spaces.AffineSiteSpecDictionary
import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalFull
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverChartSquares
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# Properties of morphisms under the affine Beauville--Laszlo equivalence (Stacks 0F9R)

Let `(g : R → R', f)` be a glueing pair and write `X = Spec R`, `U = Spec R_f`,
`U' = Spec R'_{g f}` and `X' = Spec R'`. Stacks 0F9Q makes the glueing functor of Stacks 0F9N,
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction`, an equivalence between the affine
algebraic spaces over `X` which are glueable for `(g, f)` and the cartesian glueing triples
`(V, V', Y')` over `U ← U' → X'` whose three components are affine
(`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_isEquivalence`). Stacks 0F9R says that
under this equivalence a morphism has `P` exactly when the three components of the corresponding
morphism of triples have `P`, for `P` one of: finite, closed immersion, flat, of finite type,
flat and of finite presentation, étale.

This file states and proves that, on the equivalence itself and with the properties of
morphisms of algebraic spaces of this library: `AlgebraicGeometry.Space.IsFinite`,
`AlgebraicGeometry.Space.IsClosedImmersion`, `AlgebraicGeometry.Space.IsFlat`,
`AlgebraicGeometry.Space.IsFiniteType`, `AlgebraicGeometry.Space.IsFlat` together with
`AlgebraicGeometry.Space.IsFinitePresentation`, and `AlgebraicGeometry.Space.IsEtale`.
Glueability of source and target is part of the objects of the source category, so the
statements carry no hypothesis beyond the glueing pair.

## Main results

For each of the six properties there are two statements, one for each direction of the
equivalence:

* `BeauvilleLaszlo.Space.isFinite_iff_canonicalAffineGlueableRestriction_map` and its five
  siblings: a morphism `φ` of affine glueable algebraic spaces over `X` has `P` if and only if
  the three components of its image `F.map φ` under the glueing functor `F` have `P`.
* `BeauvilleLaszlo.Space.isFinite_canonicalAffineGlueableRestriction_inv_map_iff` and its five
  siblings: for every morphism `β` of triples with affine components, the corresponding morphism
  `F.inv.map β` of algebraic spaces under the inverse equivalence has `P` if and only if the
  three components of `β` have `P`.

Together they are **Stacks 0F9R**.

## Implementation notes

The reduction is to the affine-scheme rows of
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingProperties.lean`, along the route of
`BeauvilleLaszlo.Space.isEtale_iff_isEtale_glueingComponents`, made uniform in the property: a
property `Q` of morphisms of presheaves over each base which respects isomorphisms of arrows and
which on a morphism of the site between objects with affine underlying schemes is a property `P`
of the underlying morphism of schemes. The two spaces are replaced by spectra of rings over `R`
representing them, the morphism is read in the site, and each space-level base change is
identified with the scheme-level one by an isomorphism of arrows
(`AlgebraicGeometry.relocalizeRestrictArrowIso`), so both directions hold at once.

Finite type and finite presentation of morphisms of algebraic spaces include quasi-compactness
(and, for finite presentation, quasi-separatedness); on a morphism between representables with
affine underlying schemes both hold automatically, which is how the space-level properties are
matched with `LocallyOfFiniteType` and `LocallyOfFinitePresentation` of schemes.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-! ### Respecting isomorphisms of arrows -/

section RespectsIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The square of an isomorphism of arrows `e : f ≅ f'` with horizontal sides the components of
`e.inv` is a pullback square. -/
private theorem isPullback_arrowIso {C : Type*} [Category C] {f f' : Arrow C} (e : f ≅ f') :
    IsPullback e.inv.left f'.hom f.hom e.inv.right :=
  IsPullback.of_horiz_isIso ⟨e.inv.w⟩

/-- Finiteness of morphisms of algebraic spaces respects isomorphisms of arrows. -/
private theorem isFinite_respectsIso :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsFinite B S hS k) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e hf ↦
    AlgebraicGeometry.Space.isFinite_of_isPullback B S hS (isPullback_arrowIso e) hf

/-- Quasi-compactness of morphisms of algebraic spaces respects isomorphisms of arrows. -/
private theorem isQuasiCompact_respectsIso :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsQuasiCompact B S hS k) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e hf ↦
    AlgebraicGeometry.Space.isQuasiCompact_of_isPullback B S hS (isPullback_arrowIso e) hf

/-- Quasi-separatedness of morphisms of algebraic spaces respects isomorphisms of arrows. -/
private theorem isQuasiSeparated_respectsIso :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsQuasiSeparated B S hS k) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e hf ↦
    AlgebraicGeometry.Space.isQuasiSeparated_of_isPullback B S hS (isPullback_arrowIso e) hf

/-- The conjunction of two properties respecting isomorphisms of arrows respects them. -/
private theorem respectsIso_and {C : Type*} [Category C] (P₁ P₂ : MorphismProperty C)
    [P₁.RespectsIso] [P₂.RespectsIso] :
    MorphismProperty.RespectsIso (fun {X Y : C} (k : X ⟶ Y) ↦ P₁ k ∧ P₂ k) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e hf ↦
    ⟨(P₁.arrow_mk_iso_iff e).1 hf.1, (P₂.arrow_mk_iso_iff e).1 hf.2⟩

/-- Finite type of morphisms of algebraic spaces respects isomorphisms of arrows. -/
private theorem isFiniteType_respectsIso :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsFiniteType B S hS k) :=
  @respectsIso_and _ _
    (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS k)
    (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsQuasiCompact B S hS k)
    (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _)
    (isQuasiCompact_respectsIso B S hS)

/-- Being flat and of finite presentation, for morphisms of algebraic spaces, respects
isomorphisms of arrows. -/
private theorem isFlat_and_isFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsFlat B S hS k ∧
          AlgebraicGeometry.Space.IsFinitePresentation B S hS k) :=
  @respectsIso_and _ _
    (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFlat B S hS k)
    (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFinitePresentation B S hS k)
    (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _)
    (@respectsIso_and _ _
      (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS k)
      (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsQuasiCompact B S hS k ∧
        AlgebraicGeometry.Space.IsQuasiSeparated B S hS k)
      (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _)
      (@respectsIso_and _ _
        (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsQuasiCompact B S hS k)
        (fun ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsQuasiSeparated B S hS k)
        (isQuasiCompact_respectsIso B S hS) (isQuasiSeparated_respectsIso B S hS)))

end RespectsIso

/-! ### Properties of a morphism of representables with affine underlying schemes -/

section Representable

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the site between objects with affine underlying schemes is of finite type as
a morphism of algebraic spaces exactly when its underlying morphism of schemes is locally of
finite type: quasi-compactness holds on both sides. -/
private theorem isFiniteType_yoneda_map_iff_of_isAffine {V W : BigFppfOver B S hS} (ψ : V ⟶ W)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    AlgebraicGeometry.Space.IsFiniteType B S hS (yoneda.map ψ) ↔
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ψ) :=
  ⟨fun h ↦ (AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff B S hS ψ).1 h.1,
    fun h ↦ ⟨(AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff B S hS ψ).2 h,
      AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact B S hS
        ((AlgebraicGeometry.Space.presheaf_yoneda_map_iff B S hS inferInstance ψ).2
          inferInstance)⟩⟩

/-- A morphism of the site between objects with affine underlying schemes is flat and of finite
presentation as a morphism of algebraic spaces exactly when its underlying morphism of schemes
is flat and locally of finite presentation: quasi-compactness and quasi-separatedness hold on
both sides. -/
private theorem isFlat_and_isFinitePresentation_yoneda_map_iff_of_isAffine
    {V W : BigFppfOver B S hS} (ψ : V ⟶ W)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    (AlgebraicGeometry.Space.IsFlat B S hS (yoneda.map ψ) ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map ψ)) ↔
      (Flat ((BigFppfOver.toScheme B S hS).map ψ) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ψ)) := by
  refine and_congr (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    Flat.isEtaleLocalOnSourceAndTarget ψ) ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ψ).1 h.1
  · exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ψ).2 h
  · exact AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact B S hS
      ((AlgebraicGeometry.Space.presheaf_yoneda_map_iff B S hS inferInstance ψ).2 inferInstance)
  · exact (AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff B S hS ψ).2 inferInstance

end Representable

/-! ### The two readings of a base change, as a biconditional -/

section Transport

/-- **The two readings of one base change on schemes have the same properties.** The base change
of `ψ` along a morphism `j` of the site and the base change along the morphism `ρ` of schemes
underneath `j` of the morphism of schemes underneath `ψ` are isomorphic arrows. This is the
biconditional form of `AlgebraicGeometry.prop_overPullback_map_of_prop_toScheme_pullback_map`,
with the same proof. -/
private theorem prop_toScheme_pullback_map_iff_prop_overPullback_map
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ) :
    P ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ)) ↔
      P ((Over.pullback ρ).map h).left := by
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have hTVsq : IsPullback (B.inclusion.map (pullback.fst TV.hom j))
      (B.inclusion.map (pullback.snd TV.hom j)) (B.inclusion.map TV.hom) ρ := by
    rw [← hρ]
    exact (IsPullback.of_hasPullback TV.hom j).map B.inclusion
  let i₂ := hTVsq.isoIsPullback _ _
    (IsPullback.of_hasPullback (B.inclusion.map TV.hom) ρ)
  have hi₂ : i₂.hom ≫ pullback.fst (B.inclusion.map TV.hom) ρ =
      B.inclusion.map (pullback.fst TV.hom j) :=
    hTVsq.isoIsPullback_hom_fst _ _ _
  have sqA : IsPullback ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ))
      (B.inclusion.map (pullback.fst TL.hom j)) (B.inclusion.map (pullback.fst TV.hom j))
      ((BigFppfOver.toScheme B X hX).map ψ) :=
    (OverShriek.isPullback_pullback_map j ψ).map B.inclusion
  have sqB : IsPullback ((Over.pullback ρ).map h).left
      (pullback.fst (B.inclusion.map TL.hom) ρ)
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    OverShriek.isPullback_pullback_map ρ h
  have sqA' : IsPullback
      ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ) ≫ i₂.hom)
      (B.inclusion.map (pullback.fst TL.hom j))
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    sqA.of_iso (Iso.refl _) i₂ (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using hi₂.symm) (by simp [hh])
  rw [← prop_snd_iff_of_isPullback P sqA'.flip sqB.flip, P.cancel_right_of_respectsIso]

/-- The base change along a morphism of affine bases of an object of the site with affine
underlying scheme has affine underlying scheme. -/
private theorem isAffine_toScheme_overPullback_obj (B : BigFppfSite.{u}) (X T : Scheme.{u})
    (hX : B.Contains X) (hT : B.Contains T) [IsAffine X] [IsAffine T]
    (j : B.obj hT ⟶ B.obj hX) {T₀ : BigFppfOver B X hX}
    (hT₀ : IsAffine ((BigFppfOver.toScheme B X hX).obj T₀)) :
    IsAffine ((BigFppfOver.toScheme B T hT).obj ((Over.pullback j).obj T₀)) := by
  have hpb : IsPullback (B.inclusion.map (pullback.fst T₀.hom j))
      (B.inclusion.map (pullback.snd T₀.hom j))
      (B.inclusion.map T₀.hom) (B.inclusion.map j) :=
    (IsPullback.of_hasPullback T₀.hom j).map B.inclusion
  have : IsAffine (B.inclusion.obj T₀.left) := hT₀
  have : IsAffine (B.inclusion.obj (B.obj hX)) := ‹IsAffine X›
  have : IsAffine (B.inclusion.obj (B.obj hT)) := ‹IsAffine T›
  exact IsAffine.of_isPullback hpb

/-- **One leg of a glueing triple, as a biconditional.** For a property `Q` of morphisms of
presheaves over `T` which respects isomorphisms of arrows and which on morphisms of the site
between objects with affine underlying schemes is the property `P` of the underlying morphism of
schemes, the restriction along `j` of a morphism `p` represented by `ψ` has `Q` exactly when the
base change along the underlying morphism of schemes `ρ` of a morphism `h` of schemes over `X`
underlying `ψ` has `P`. -/
private theorem prop_relocalizeRestrict_map_iff_prop_overPullback_map
    (B : BigFppfSite.{u}) (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T)
    [IsAffine X] [IsAffine T]
    (Q : MorphismProperty ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u)) [Q.RespectsIso]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hQP : ∀ {V W : BigFppfOver B T hT} (ψ : V ⟶ W),
      IsAffine ((BigFppfOver.toScheme B T hT).obj V) →
      IsAffine ((BigFppfOver.toScheme B T hT).obj W) →
      (Q (yoneda.map ψ) ↔ P ((BigFppfOver.toScheme B T hT).map ψ)))
    (j : B.obj hT ⟶ B.obj hX) (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX}
    (hTL : IsAffine ((BigFppfOver.toScheme B X hX).obj TL))
    (hTV : IsAffine ((BigFppfOver.toScheme B X hX).obj TV)) (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom) :
    Q ((OverShriek.relocalizeRestrict j).map p) ↔ P ((Over.pullback ρ).map h).left :=
  ((Q.arrow_mk_iso_iff (relocalizeRestrictArrowIso B X T hX hT j ψ p eL eV hψ)).trans
    (hQP _ (isAffine_toScheme_overPullback_obj B X T hX hT j hTL)
      (isAffine_toScheme_overPullback_obj B X T hX hT j hTV))).trans
    (prop_toScheme_pullback_map_iff_prop_overPullback_map P B X T hX hT j ρ hρ ψ h hh)

end Transport

/-! ### The generic statement -/

section Generic

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))

/-- The composite leg `U' ⟶ U ⟶ X` of the Beauville--Laszlo square is, on schemes, the structure
morphism of `Spec R'_{g f}` over `Spec R`. -/
private theorem inclusion_map_canGU_comp_canJU :
    letI : Algebra R R' := g.toAlgebra
    B.inclusion.map (canGU g f B hU' hU ≫ canJU f B hU hX) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (algebraMap R R' f)))) := by
  let : Algebra R R' := g.toAlgebra
  rw [Functor.map_comp]
  simp only [ObjectProperty.ι_map, ← Spec.map_comp]
  congr 1
  ext r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The affine-scheme form of Stacks 0F9R for a property `P` of morphisms of schemes: a morphism
`Spec A → Spec C` of schemes over `Spec R` with `C` glueable has `P` exactly when its base
changes to `U`, `U'` and `X'` do. -/
private def AffineSchemeRow (P : MorphismProperty Scheme.{u}) : Prop :=
  letI : Algebra R R' := g.toAlgebra
  ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C],
    (_root_.BeauvilleLaszlo.beauvilleLaszloModuleSequence (S := R') C f).ShortExact →
    ∀ h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C))),
    P h.left ↔
      P ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        P ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          P ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map h).left

/-- **Stacks 0F9R for a general property, for a morphism of affine algebraic spaces with
glueable target.** Let `Q` be a property of morphisms of presheaves over each base of the site
which respects isomorphisms of arrows and which on a morphism of the site between objects with
affine underlying schemes is a property `P` of the underlying morphism of schemes, and assume
the affine-scheme form of the statement for `P`. Then a morphism `p : L ⟶ V` of algebraic spaces
over `X = Spec R`, with `L` and `V` affine and `V` glueable, has `Q` if and only if its base
changes to `U`, `U'` and `X'` have `Q`. -/
private theorem prop_iff_prop_baseChange_of_isAffineSpace
    (Q : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      MorphismProperty ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u))
    (hQi : ∀ (T : Scheme.{u}) (hT : B.Contains T), (Q T hT).RespectsIso)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hQP : ∀ (T : Scheme.{u}) (hT : B.Contains T) {V W : BigFppfOver B T hT} (ψ : V ⟶ W),
      IsAffine ((BigFppfOver.toScheme B T hT).obj V) →
      IsAffine ((BigFppfOver.toScheme B T hT).obj W) →
      (Q T hT (yoneda.map ψ) ↔ P ((BigFppfOver.toScheme B T hT).map ψ)))
    (hscheme : AffineSchemeRow g f P)
    {L V : AlgebraicSpaces B (Spec (.of R)) hX} (p : L ⟶ V)
    (hLa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX L.1)
    (hVa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX V.1)
    (hVg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX V) :
    Q _ hX p.hom ↔
      Q _ hU ((OverShriek.relocalizeRestrict (canJU f B hU hX)).map p.hom) ∧
        Q _ hU' ((OverShriek.relocalizeRestrict
          (canGU g f B hU' hU ≫ canJU f B hU hX)).map p.hom) ∧
          Q _ hX' ((OverShriek.relocalizeRestrict (canJX' g B hX' hX)).map p.hom) := by
  let : Algebra R R' := g.toAlgebra
  obtain ⟨TL, hTL, ⟨eL0⟩⟩ := hLa
  obtain ⟨A, hA, φA, ⟨eL1⟩⟩ := BigFppfOver.exists_specOver B hX TL hTL
  obtain ⟨TV, hTV, ⟨eV0⟩⟩ := hVa
  obtain ⟨C, hC, φC, ⟨eV1⟩⟩ := BigFppfOver.exists_specOver B hX TV hTV
  let : Algebra R A := φA.hom.toAlgebra
  let : Algebra R C := φC.hom.toAlgebra
  obtain ⟨eL, eV, ψ, hψ⟩ :
      ∃ (eL : L.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hA φA))
        (eV : V.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hC φC))
        (ψ : BigFppfOver.specOver B hX hA φA ⟶ BigFppfOver.specOver B hX hC φC),
        yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom :=
    ⟨eL0 ≪≫ yoneda.mapIso eL1, eV0 ≪≫ yoneda.mapIso eV1,
      yoneda.preimage ((eL0 ≪≫ yoneda.mapIso eL1).inv ≫ p.hom ≫
        (eV0 ≪≫ yoneda.mapIso eV1).hom), yoneda.map_preimage _⟩
  have hCgs : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX
      (BigFppfOver.specOver B hX hC φC) :=
    hVg (BigFppfOver.specOver B hX hC φC) eV.inv
      (BigFppfOver.isAffine_toScheme_obj_specOver B hX hC φC)
      (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX eV.inv)
  have hCg : (_root_.BeauvilleLaszlo.beauvilleLaszloModuleSequence (S := R')
      (C : Type u) f).ShortExact :=
    (_root_.BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact _ f).1
      (isGlueableFor_of_isGlueableGlobalSections g f B hX (C : Type u) hC hCgs)
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A : Type u)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (C : Type u)))) :=
    Over.homMk ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ)
      (BigFppfOver.specOverHomMap_comp B hX hA hC φA φC ψ)
  have hh : h.left = (BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ := rfl
  have hAa := BigFppfOver.isAffine_toScheme_obj_specOver B hX hA φA
  have hCa := BigFppfOver.isAffine_toScheme_obj_specOver B hX hC φC
  have := hQi _ hX
  have hspace : Q _ hX p.hom ↔ P h.left :=
    ((Q _ hX).arrow_mk_iso_iff (yonedaMapArrowIso B _ hX ψ p.hom eL eV hψ)).symm.trans
      (hQP _ hX ψ hAa hCa)
  have := hQi _ hU
  have := hQi _ hU'
  have := hQi _ hX'
  refine hspace.trans ((hscheme A C hCg h).trans (and_congr ?_ (and_congr ?_ ?_)).symm)
  · exact prop_relocalizeRestrict_map_iff_prop_overPullback_map B _ _ hX hU (Q _ hU) P
      (hQP _ hU) (canJU f B hU hX) _ rfl hAa hCa ψ h hh p.hom eL eV hψ
  · exact prop_relocalizeRestrict_map_iff_prop_overPullback_map B _ _ hX hU' (Q _ hU') P
      (hQP _ hU') (canGU g f B hU' hU ≫ canJU f B hU hX) _
      (inclusion_map_canGU_comp_canJU g f B hU' hU hX) hAa hCa ψ h hh p.hom eL eV hψ
  · exact prop_relocalizeRestrict_map_iff_prop_overPullback_map B _ _ hX hX' (Q _ hX') P
      (hQP _ hX') (canJX' g B hX' hX) _ rfl hAa hCa ψ h hh p.hom eL eV hψ

/-- **The generic statement on the equivalence of Stacks 0F9Q, forward direction.** For `Q` and
`P` as in `BeauvilleLaszlo.Space.prop_iff_prop_baseChange_of_isAffineSpace`, a morphism `φ` of
affine glueable algebraic spaces over `X` has `Q` exactly when the three components of its image
under the glueing functor have `Q`. -/
private theorem prop_iff_prop_canonicalAffineGlueableRestriction_map
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (Q : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      MorphismProperty ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u))
    (hQi : ∀ (T : Scheme.{u}) (hT : B.Contains T), (Q T hT).RespectsIso)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hQP : ∀ (T : Scheme.{u}) (hT : B.Contains T) {V W : BigFppfOver B T hT} (ψ : V ⟶ W),
      IsAffine ((BigFppfOver.toScheme B T hT).obj V) →
      IsAffine ((BigFppfOver.toScheme B T hT).obj W) →
      (Q T hT (yoneda.map ψ) ↔ P ((BigFppfOver.toScheme B T hT).map ψ)))
    (hscheme : AffineSchemeRow g f P)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    Q _ hX φ.hom.hom ↔
      Q _ hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map φ).hom).hom ∧
        Q _ hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map φ).hom).hom ∧
          Q _ hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map φ).hom).hom :=
  prop_iff_prop_baseChange_of_isAffineSpace g f B hU' hU hX' hX Q hQi P hQP hscheme φ.hom
    Y.property.1 Z.property.1 Z.property.2

/-- **The generic statement on the equivalence of Stacks 0F9Q, backward direction.** For `Q`
and `P` as in `BeauvilleLaszlo.Space.prop_iff_prop_baseChange_of_isAffineSpace`, the morphism of
affine glueable algebraic spaces corresponding to a morphism `β` of triples with affine
components under the inverse of the equivalence of Stacks 0F9Q has `Q` exactly when the three
components of `β` have `Q`. -/
private theorem prop_affineGlueingEquivalence_inverse_map_iff
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (Q : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      MorphismProperty ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u))
    (hQi : ∀ (T : Scheme.{u}) (hT : B.Contains T), (Q T hT).RespectsIso)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hQP : ∀ (T : Scheme.{u}) (hT : B.Contains T) {V W : BigFppfOver B T hT} (ψ : V ⟶ W),
      IsAffine ((BigFppfOver.toScheme B T hT).obj V) →
      IsAffine ((BigFppfOver.toScheme B T hT).obj W) →
      (Q T hT (yoneda.map ψ) ↔ P ((BigFppfOver.toScheme B T hT).map ψ)))
    (hscheme : AffineSchemeRow g f P)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    Q _ hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      Q _ hU ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        Q _ hU' ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          Q _ hX' ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  let e := Arrow.isoOfNatIso
    (affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.counitIso (Arrow.mk β)
  have := hQi _ hU
  have hU₀ := (Q _ hU).arrow_iso_iff
    ((ObjectProperty.ι _ ⋙ overU B _ _ _ hU' hU hX' _ _ ⋙ ObjectProperty.ι _).mapArrow.mapIso e)
  have := hQi _ hU'
  have hU'₀ := (Q _ hU').arrow_iso_iff
    ((ObjectProperty.ι _ ⋙ overU' B _ _ _ hU' hU hX' _ _ ⋙ ObjectProperty.ι _).mapArrow.mapIso e)
  have := hQi _ hX'
  have hX'₀ := (Q _ hX').arrow_iso_iff
    ((ObjectProperty.ι _ ⋙ overX' B _ _ _ hU' hU hX' _ _ ⋙ ObjectProperty.ι _).mapArrow.mapIso e)
  exact (prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm Q hQi P
    hQP hscheme
    ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map β)).trans
    (and_congr hU₀ (and_congr hU'₀ hX'₀))

end Generic

/-! ### Stacks 0F9R, one property at a time -/

/-- **Stacks 0F9R for `P` finite, on the glueing functor.** Let `(g : R → R', f)` be a glueing pair
and let `F` be the glueing functor of Stacks 0F9N restricted, as in Stacks 0F9Q, to the affine
algebraic spaces over `X = Spec R` which are glueable for `(g, f)`. A morphism `φ` of such
spaces is finite if and only if the three components of the morphism of triples `F.map φ`, over
`U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'`, are finite. -/
@[stacks 0F9R "P = finite; morphisms of affine glueable spaces"]
theorem isFinite_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsFinite B (Spec (.of R)) hX φ.hom.hom ↔
      AlgebraicGeometry.Space.IsFinite B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
              φ).hom).hom ∧
        AlgebraicGeometry.Space.IsFinite B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsFinite B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFinite B T hT k)
    (fun T hT ↦ isFinite_respectsIso B T hT)
    @AlgebraicGeometry.IsFinite.{u}
    (fun T hT _ _ ψ _ _ ↦ AlgebraicGeometry.Space.isFinite_yoneda_map_iff B T hT ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.isFinite_iff_baseChange f hglue h) φ

/-- **Stacks 0F9R for `P` finite, on the inverse equivalence.** Let `(g : R → R', f)` be a glueing
pair. For every morphism `β` of glueing triples over `U ← U' → X'` with affine components, the
morphism of affine glueable algebraic spaces over `X = Spec R` corresponding to `β` under the
equivalence of Stacks 0F9Q is finite if and only if the three components of `β` are finite. -/
@[stacks 0F9R "P = finite; morphisms of triples with affine components"]
theorem isFinite_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    AlgebraicGeometry.Space.IsFinite B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      AlgebraicGeometry.Space.IsFinite B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        AlgebraicGeometry.Space.IsFinite B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsFinite B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFinite B T hT k)
    (fun T hT ↦ isFinite_respectsIso B T hT)
    @AlgebraicGeometry.IsFinite.{u}
    (fun T hT _ _ ψ _ _ ↦ AlgebraicGeometry.Space.isFinite_yoneda_map_iff B T hT ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.isFinite_iff_baseChange f hglue h) β

/-- **Stacks 0F9R for `P` closed immersion, on the glueing functor.** Let `(g : R → R', f)` be a
glueing pair and let `F` be the glueing functor of Stacks 0F9N restricted, as in Stacks 0F9Q, to
the affine algebraic spaces over `X = Spec R` which are glueable for `(g, f)`. A morphism `φ` of
such spaces is a closed immersion if and only if the three components of the morphism of triples
`F.map φ`, over `U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'`, are closed immersions. -/
@[stacks 0F9R "P = closed immersion; morphisms of affine glueable spaces"]
theorem isClosedImmersion_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R)) hX φ.hom.hom ↔
      AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
              φ).hom).hom ∧
        AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsClosedImmersion B T hT k)
    (fun _ _ ↦ inferInstance)
    @AlgebraicGeometry.IsClosedImmersion.{u}
    (fun T hT _ _ ψ _ _ ↦
      AlgebraicGeometry.Space.presheaf_yoneda_map_iff B T hT inferInstance ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.isClosedImmersion_iff_baseChange f hglue h) φ

/-- Let `(g : R → R', f)` be a glueing pair. For every morphism `β` of glueing triples over
`U ← U' → X'` with affine components, the morphism of affine glueable algebraic spaces over
`X = Spec R` corresponding to `β` under the inverse of the glueing equivalence is a closed
immersion if and only if the three components of `β` are closed immersions. -/
@[stacks 0F9R "P = closed immersion; morphisms of triples with affine components"]
theorem isClosedImmersion_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsClosedImmersion B T hT k)
    (fun _ _ ↦ inferInstance)
    @AlgebraicGeometry.IsClosedImmersion.{u}
    (fun T hT _ _ ψ _ _ ↦
      AlgebraicGeometry.Space.presheaf_yoneda_map_iff B T hT inferInstance ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.isClosedImmersion_iff_baseChange f hglue h) β

/-- **Stacks 0F9R for `P` flat, on the glueing functor.** Let `(g : R → R', f)` be a glueing pair
and let `F` be the glueing functor of Stacks 0F9N restricted, as in Stacks 0F9Q, to the affine
algebraic spaces over `X = Spec R` which are glueable for `(g, f)`. A morphism `φ` of such
spaces is flat if and only if the three components of the morphism of triples `F.map φ`, over
`U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'`, are flat. -/
@[stacks 0F9R "P = flat; morphisms of affine glueable spaces"]
theorem isFlat_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX φ.hom.hom ↔
      AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
              φ).hom).hom ∧
        AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsFlat B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFlat B T hT k)
    (fun T hT ↦
      AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B T hT _)
    @AlgebraicGeometry.Flat.{u}
    (fun T hT _ _ ψ _ _ ↦ AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B T hT
      Flat.isEtaleLocalOnSourceAndTarget ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.flat_iff_baseChange f hglue hC h) φ

/-- **Stacks 0F9R for `P` flat, on the inverse equivalence.** Let `(g : R → R', f)` be a glueing
pair. For every morphism `β` of glueing triples over `U ← U' → X'` with affine components, the
morphism of affine glueable algebraic spaces over `X = Spec R` corresponding to `β` under the
equivalence of Stacks 0F9Q is flat if and only if the three components of `β` are flat. -/
@[stacks 0F9R "P = flat; morphisms of triples with affine components"]
theorem isFlat_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsFlat B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFlat B T hT k)
    (fun T hT ↦
      AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B T hT _)
    @AlgebraicGeometry.Flat.{u}
    (fun T hT _ _ ψ _ _ ↦ AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B T hT
      Flat.isEtaleLocalOnSourceAndTarget ψ)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.flat_iff_baseChange f hglue hC h) β

/-- **Stacks 0F9R for `P` finite type, on the glueing functor.** Let `(g : R → R', f)` be a glueing
pair and let `F` be the glueing functor of Stacks 0F9N restricted, as in Stacks 0F9Q, to the
affine algebraic spaces over `X = Spec R` which are glueable for `(g, f)`. A morphism `φ` of
such spaces is of finite type if and only if the three components of the morphism of triples
`F.map φ`, over `U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'`, are of finite type. -/
@[stacks 0F9R "P = finite type; morphisms of affine glueable spaces"]
theorem isFiniteType_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsFiniteType B (Spec (.of R)) hX φ.hom.hom ↔
      AlgebraicGeometry.Space.IsFiniteType B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
              φ).hom).hom ∧
        AlgebraicGeometry.Space.IsFiniteType B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsFiniteType B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFiniteType B T hT k)
    (fun T hT ↦ isFiniteType_respectsIso B T hT)
    @AlgebraicGeometry.LocallyOfFiniteType.{u}
    (fun T hT _ _ ψ hV hW ↦ isFiniteType_yoneda_map_iff_of_isAffine B T hT ψ hV hW)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.locallyOfFiniteType_iff_baseChange f hglue h) φ

/-- **Stacks 0F9R for `P` finite type, on the inverse equivalence.** Let `(g : R → R', f)` be a
glueing pair. For every morphism `β` of glueing triples over `U ← U' → X'` with affine
components, the morphism of affine glueable algebraic spaces over `X = Spec R` corresponding to
`β` under the equivalence of Stacks 0F9Q is of finite type if and only if the three components
of `β` are of finite type. -/
@[stacks 0F9R "P = finite type; morphisms of triples with affine components"]
theorem isFiniteType_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    AlgebraicGeometry.Space.IsFiniteType B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      AlgebraicGeometry.Space.IsFiniteType B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        AlgebraicGeometry.Space.IsFiniteType B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsFiniteType B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFiniteType B T hT k)
    (fun T hT ↦ isFiniteType_respectsIso B T hT)
    @AlgebraicGeometry.LocallyOfFiniteType.{u}
    (fun T hT _ _ ψ hV hW ↦ isFiniteType_yoneda_map_iff_of_isAffine B T hT ψ hV hW)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ _ h ↦
        _root_.BeauvilleLaszlo.locallyOfFiniteType_iff_baseChange f hglue h) β

/-- **Stacks 0F9R for `P` flat and finite presentation, on the glueing functor.** Let
`(g : R → R', f)` be a glueing pair and let `F` be the glueing functor of Stacks 0F9N
restricted, as in Stacks 0F9Q, to the affine algebraic spaces over `X = Spec R` which are
glueable for `(g, f)`. A morphism `φ` of such spaces is flat and of finite presentation if and
only if the three components of the morphism of triples `F.map φ`, over `U = Spec R_f`,
`U' = Spec R'_{g f}` and `X' = Spec R'`, are flat and of finite presentation. -/
@[stacks 0F9R "P = flat and finite presentation; morphisms of affine glueable spaces"]
theorem isFlat_and_isFinitePresentation_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    (AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX φ.hom.hom ∧
        AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of R)) hX φ.hom.hom) ↔
      (AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away f))) hU
            ((overU B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of (Localization.Away f))) hU
            ((overU B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom) ∧
        (AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away (g f)))) hU'
              ((overU' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom ∧
            AlgebraicGeometry.Space.IsFinitePresentation B
                (Spec (.of (Localization.Away (g f)))) hU'
              ((overU' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom) ∧
          (AlgebraicGeometry.Space.IsFlat B (Spec (.of R')) hX'
                ((overX' B _ _ _ hU' hU hX' _ _).map
                  ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                    φ).hom).hom ∧
              AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of R')) hX'
                ((overX' B _ _ _ hU' hU hX' _ _).map
                  ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                    φ).hom).hom) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFlat B T hT k ∧
      AlgebraicGeometry.Space.IsFinitePresentation B T hT k)
    (fun T hT ↦ isFlat_and_isFinitePresentation_respectsIso B T hT)
    (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (fun T hT _ _ ψ hV hW ↦
      isFlat_and_isFinitePresentation_yoneda_map_iff_of_isAffine B T hT ψ hV hW)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.flat_and_locallyOfFinitePresentation_iff_baseChange f hglue
        hC h) φ

/-- **Stacks 0F9R for `P` flat and finite presentation, on the inverse equivalence.** Let
`(g : R → R', f)` be a glueing pair. For every morphism `β` of glueing triples over
`U ← U' → X'` with affine components, the morphism of affine glueable algebraic spaces over
`X = Spec R` corresponding to `β` under the equivalence of Stacks 0F9Q is flat and of finite
presentation if and only if the three components of `β` are flat and of finite presentation. -/
@[stacks 0F9R "P = flat and finite presentation; morphisms of triples with affine components"]
theorem isFlat_and_isFinitePresentation_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    (AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ∧
      AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom) ↔
      (AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away f))) hU
            ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of (Localization.Away f))) hU
            ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom) ∧
        (AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away (g f)))) hU'
              ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
            AlgebraicGeometry.Space.IsFinitePresentation B
                (Spec (.of (Localization.Away (g f)))) hU'
              ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom) ∧
          (AlgebraicGeometry.Space.IsFlat B (Spec (.of R')) hX'
                ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
              AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of R')) hX'
                ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsFlat B T hT k ∧
      AlgebraicGeometry.Space.IsFinitePresentation B T hT k)
    (fun T hT ↦ isFlat_and_isFinitePresentation_respectsIso B T hT)
    (@AlgebraicGeometry.Flat.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (fun T hT _ _ ψ hV hW ↦
      isFlat_and_isFinitePresentation_yoneda_map_iff_of_isAffine B T hT ψ hV hW)
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.flat_and_locallyOfFinitePresentation_iff_baseChange f hglue
        hC h) β

/-- **Stacks 0F9R for `P` étale, on the glueing functor.** Let `(g : R → R', f)` be a glueing pair
and let `F` be the glueing functor of Stacks 0F9N restricted, as in Stacks 0F9Q, to the affine
algebraic spaces over `X = Spec R` which are glueable for `(g, f)`. A morphism `φ` of such
spaces is étale if and only if the three components of the morphism of triples `F.map φ`, over
`U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'`, are étale. -/
@[stacks 0F9R "P = étale; morphisms of affine glueable spaces"]
theorem isEtale_iff_canonicalAffineGlueableRestriction_map
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {Y Z : (affineGlueableSpaces g f B hX).FullSubcategory} (φ : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX φ.hom.hom ↔
      AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map
            ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
              φ).hom).hom ∧
        AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map
              ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                φ).hom).hom ∧
          AlgebraicGeometry.Space.IsEtale B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map
                ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
                  φ).hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_iff_prop_canonicalAffineGlueableRestriction_map g f B hU' hU hX' hX hcomm
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsEtale B T hT k)
    (fun T hT ↦ isEtale_respectsIso B T hT)
    @AlgebraicGeometry.Etale.{u}
    (fun T hT _ _ ψ _ _ ↦
      (AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B T hT _).trans
        (AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff B T hT ψ))
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.etale_iff_baseChange f hglue hC h) φ

/-- **Stacks 0F9R for `P` étale, on the inverse equivalence.** Let `(g : R → R', f)` be a glueing
pair. For every morphism `β` of glueing triples over `U ← U' → X'` with affine components, the
morphism of affine glueable algebraic spaces over `X = Spec R` corresponding to `β` under the
equivalence of Stacks 0F9Q is étale if and only if the three components of `β` are étale. -/
@[stacks 0F9R "P = étale; morphisms of triples with affine components"]
theorem isEtale_affineGlueingEquivalence_inverse_map_iff
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    {T₁ T₂ : (affineComponents B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).FullSubcategory} (β : T₁ ⟶ T₂) :
    AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX
        ((affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue).equivalence.inverse.map
          β).hom.hom ↔
      AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away f))) hU
          ((overU B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
        AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away (g f)))) hU'
            ((overU' B _ _ _ hU' hU hX' _ _).map β.hom).hom ∧
          AlgebraicGeometry.Space.IsEtale B (Spec (.of R')) hX'
              ((overX' B _ _ _ hU' hU hX' _ _).map β.hom).hom := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_affineGlueingEquivalence_inverse_map_iff g f B hU' hU hX' hX hcomm hglue
    (fun T hT ⦃_ _⦄ k ↦ AlgebraicGeometry.Space.IsEtale B T hT k)
    (fun T hT ↦ isEtale_respectsIso B T hT)
    @AlgebraicGeometry.Etale.{u}
    (fun T hT _ _ ψ _ _ ↦
      (AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B T hT _).trans
        (AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff B T hT ψ))
    (by
      let : Algebra R R' := g.toAlgebra
      exact fun _ _ _ _ _ _ hC h ↦
        _root_.BeauvilleLaszlo.etale_iff_baseChange f hglue hC h) β

end BeauvilleLaszlo.Space

end

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.Order.ULift
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.FiniteLimitPresentation
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# Finite algebra sheaves as directed colimits, from a limit presentation of the relative spectrum

Let `X` be a quasi-compact and quasi-separated scheme and let `A` be a finite quasi-coherent
sheaf of `𝒪_X`-algebras.  Under the anti-equivalence of [Stacks, Tag 01SA] the algebra `A` is
`Y_* 𝒪_Y` for a scheme `Y` finite over `X`, and [Stacks, Tag 09YY] presents such a `Y` as the
inverse limit of a directed system of schemes finite and of finite presentation over `X` with
closed-immersion transition maps.  Transporting that limit through the anti-equivalence turns it
into a directed colimit presentation of `A` by finite, finitely presented quasi-coherent
algebras with surjective transition maps, which is the assertion of [Stacks, Tag 086N].

This file proves that transport, and then constructs the limit presentation it consumes, so
that Tag 086N holds outright.  The transport is stated against the explicit hypothesis
`FiniteLimitPresentation`, transcribed from the statement of Tag 09YY, and discharges
everything in Tag 086N *other than* Tag 09YY: the whole passage from schemes to algebra
sheaves.  Tag 09YY is then proved in `finiteLimitPresentationOfIsFinite`: a finite morphism is
locally of finite type, so [Stacks, Tag 09ZQ] presents it as an inverse limit of morphisms of
finite presentation with closed-immersion transition maps, and [Stacks, Tag 09ZN] makes those
stages finite over the base from some index onwards, so restricting the system to that cofinal
tail — a restriction along an initial functor, which preserves the limit — gives a presentation
all of whose stages are finite.

Tag `086N` is carried by `exists_isColimit_finite_finitePresentation`, the unconditional
statement; `exists_isColimit_finite_finitePresentation_of_finiteLimitPresentation` is the
same conclusion with the limit presentation as an explicit hypothesis.

## Main definitions

* `FiniteLimitPresentation f` records a directed inverse system of schemes over the base
  together with a limiting cone from the source, with every stage finite and of finite
  presentation over the base and every transition map a closed immersion.  This is the data of
  [Stacks, Tag 09YY].
* `AlgebraSheaf.Hom.IsSurjective` is local surjectivity of the underlying morphism of
  presheaves of rings, as in the statement of Tag 086N.

## Main results

* `isColimit_of_isLimit_affineOver` transports a limit cone of schemes affine over `X`, over a
  connected index category, to a colimit cocone of quasi-coherent algebras.  This is the
  mathematical core: the comparison is checked on the sections over each affine open, where the
  limit of affines is computed by global sections, and a morphism of sheaves is determined by
  its restriction to the affine opens.
* `isSurjective_map_of_isClosedImmersion`: the algebra map attached to a closed immersion of
  schemes affine over `X` is locally surjective.
* `exists_isColimit_finite_finitePresentation_of_finiteLimitPresentation`: the conclusion of
  [Stacks, Tag 086N], given a limit presentation of the relative spectrum.
* `finiteLimitPresentationOfIsFinite`: **[Stacks, Tag 09YY]** — a finite morphism over a
  quasi-compact and quasi-separated base carries such a limit presentation.
* `exists_isColimit_finite_finitePresentation`: **[Stacks, Tag 086N]** — a finite quasi-coherent
  algebra on a quasi-compact and quasi-separated scheme is a directed colimit of finite,
  finitely presented quasi-coherent algebras with surjective transition maps.

## Implementation notes

The restriction functor `restrictOver U : Over X ⥤ Scheme` sending `Y` to the open subscheme
`Y.hom ⁻¹ᵁ U` is shown isomorphic to pulling back along `U.ι` and forgetting, which is how it
inherits preservation of connected limits; this is what lets the sections over an affine open
`U` be computed as a colimit.

`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` and the finiteness predicates of
`Stacks.RelativeSpec.AlgebraSheaf` realize the pushforward algebra of Tag 01SA and the finiteness
and finite presentation
predicates on sheaves of algebras of Tag 05JS used in the tagged statement.

`FiniteLimitPresentation.indexType` is declared in `Type (u + 1)`, in faithfulness to Tag 09YY,
whereas [Stacks, Tag 09ZQ] supplies its index in `Type u`; the cofinal tail is therefore
transported along `ULift` when the presentation is assembled.  Keeping the index small up to
that point is what lets [Stacks, Tag 09ZN] be applied in the form whose index type and scheme
type share a universe, which is the form the repository proves with no smallness hypothesis.

## References

* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 09YY](https://stacks.math.columbia.edu/tag/09YY)
* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
* [Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf.Hom

/-- A morphism of algebra sheaves is *surjective* when it is locally surjective as a morphism
of presheaves of rings.  This is the surjectivity in the conclusion of [Stacks, Tag 086N]. -/
def IsSurjective {X : Scheme.{u}} {A B : AlgebraSheaf X} (f : A ⟶ B) : Prop :=
  Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.right.hom

end Stacks.RelativeSpec.AlgebraSheaf.Hom

namespace Stacks.FiniteAlgebraLimitPresentation

/-- A presentation of a morphism as a directed inverse limit of finite, finitely presented
morphisms to its base, with closed-immersion transition maps.  This is the data asserted to
exist by [Stacks, Tag 09YY] for a finite morphism over a quasi-compact and quasi-separated
base.

The index preorder is allowed to live one universe above the schemes, exactly as in that tag;
the field `compactOpenDescends` is recorded for faithfulness to the tag and is not used below. -/
structure FiniteLimitPresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The directed index preorder. -/
  indexType : Type (u + 1)
  [indexPreorder : Preorder indexType]
  [indexNonempty : Nonempty indexType]
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The inverse system of schemes. -/
  diagram : indexTypeᵒᵖ ⥤ Scheme.{u}
  /-- The compatible maps of the stages to the base. -/
  structureMap : diagram ⟶ (Functor.const indexTypeᵒᵖ).obj S
  /-- The cone from the original scheme to the inverse system. -/
  limitCone : (Functor.const indexTypeᵒᵖ).obj X ⟶ diagram
  /-- The composite through every stage is the original morphism. -/
  compatible : ∀ i, f = limitCone.app i ≫ structureMap.app i
  /-- The cone exhibits the original scheme as the limit. -/
  isLimit : IsLimit (Cone.mk X limitCone)
  /-- Every quasi-compact open of the limit comes from a quasi-compact open at a finite stage. -/
  compactOpenDescends : ∀ (U : X.Opens) (_ : IsCompact (U : Set X)),
    ∃ (i : indexTypeᵒᵖ) (V : (diagram.obj i).Opens),
      IsCompact (V : Set (diagram.obj i)) ∧ limitCone.app i ⁻¹ᵁ V = U
  /-- Every stage is finite over the base. -/
  stageFinite : ∀ i, IsFinite (structureMap.app i)
  /-- Every stage is of finite presentation over the base. -/
  stageFinitePresentation : ∀ i, FinitePresentation (structureMap.app i)
  /-- Every transition map is a closed immersion. -/
  transitionClosed : ∀ {i j : indexType} (h : i ≤ j),
    IsClosedImmersion (diagram.map (homOfLE h).op)

/-! ### Restricting a scheme over `X` to the part lying over an open of `X` -/

/-- For a morphism `f : Y ⟶ Z` over `X`, the part of `Y` over `U` maps into the part of `Z`
over `U`. -/
lemma over_preimage_le {X : Scheme.{u}} {Y Z : Over X} (f : Y ⟶ Z)
    (U : X.Opens) : Y.hom ⁻¹ᵁ U ≤ f.left ⁻¹ᵁ (Z.hom ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, Over.w]

/-- The functor sending a scheme over `X` to the open subscheme lying over `U`. -/
noncomputable def restrictOver {X : Scheme.{u}} (U : X.Opens) :
    Over X ⥤ Scheme.{u} where
  obj Y := (Y.hom ⁻¹ᵁ U).toScheme
  map f := f.left.resLE _ _ (over_preimage_le f U)
  map_id Y := by
    apply (cancel_mono (Y.hom ⁻¹ᵁ U).ι).mp
    simp
  map_comp {Y Z W} f g := by
    apply (cancel_mono (W.hom ⁻¹ᵁ U).ι).mp
    simp [Scheme.Hom.resLE_comp_ι, reassoc_of% Scheme.Hom.resLE_comp_ι]

/-- Restricting to the part over `U` is pulling back along `U.ι`. -/
noncomputable def pullbackRestrictOverIso {X : Scheme.{u}} (U : X.Opens) :
    Over.pullback U.ι ⋙ Over.forget U.toScheme ≅ restrictOver U :=
  NatIso.ofComponents (fun Y => pullbackRestrictIsoRestrict Y.hom U) (by
    intro Y Z f
    apply (cancel_mono (Z.hom ⁻¹ᵁ U).ι).mp
    simp [restrictOver, Over.pullback_map_left])

/-! ### The sections of a pushed-forward structure sheaf -/

/-- On sections over `U`, the transport along an equality `f = g` of the pushed-forward
algebras is the restriction along the equality `g ⁻¹ᵁ U = f ⁻¹ᵁ U`. -/
lemma pushforwardAlgebra_eqToHom_app {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (U : X.Opens) :
    (eqToHom (congrArg pushforwardAlgebra h)).right.hom.app (.op U) =
      Y.presheaf.map (eqToHom (show g ⁻¹ᵁ U = f ⁻¹ᵁ U by rw [h])).op := by
  subst g
  simp
  rfl

/-- On sections over `U`, the algebra map attached to a morphism `f` over `X` is
`f.left.appLE`. -/
lemma pushforwardAlgebraMap_app {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) (U : X.Opens) :
    (pushforwardAlgebraMap f).right.hom.app (.op U) =
      f.left.appLE (Z.hom ⁻¹ᵁ U) (Y.hom ⁻¹ᵁ U) (over_preimage_le f U) := by
  change f.left.app (Z.hom ⁻¹ᵁ U) ≫
    (eqToHom (congrArg pushforwardAlgebra (Over.w f))).right.hom.app (.op U) = _
  rw [pushforwardAlgebra_eqToHom_app (Over.w f) U]
  rfl

/-- Over an open `U` of `X`, the sections of the algebra attached to a scheme affine over `X`
are the global sections of the part of that scheme lying over `U`. -/
noncomputable def affineSectionsIso (E : AffineAlgebraAntiEquivalence.{u})
    (X : Scheme.{u}) (U : X.Opens) :
    ((IsAffineHomOver X).ι ⋙ restrictOver U).op ⋙ Scheme.Γ ≅
      (E.equivalence X).functor ⋙ (IsQuasicoherentAlgebra X).ι ⋙
        Under.forget X.sheaf ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (.op U) :=
  NatIso.ofComponents (fun Y =>
    (Y.unop.obj.hom ⁻¹ᵁ U).topIso ≪≫
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (.op U)).mapIso
        ((Under.forget X.sheaf).mapIso (E.pushforwardIso X Y.unop))).symm) (by
    intro Y Z f
    let ev := Under.forget X.sheaf ⋙ sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (.op U)
    let eY := ev.mapIso (E.pushforwardIso X Y.unop)
    let eZ := ev.mapIso (E.pushforwardIso X Z.unop)
    let tZ := (Z.unop.obj.hom ⁻¹ᵁ U).topIso
    -- `AY` is the algebra map on the sections over `U`, `MY` its image under the
    -- anti-equivalence.
    let AY := (pushforwardAlgebraMap ((IsAffineHomOver X).ι.map f.unop)).right.hom.app (.op U)
    let MY := ((IsQuasicoherentAlgebra X).ι.map
      ((E.equivalence X).functor.map f.unop.op)).right.hom.app (.op U)
    have h : MY ≫ eZ.hom = eY.hom ≫ AY :=
      congrArg ev.map (E.pushforwardIso_naturality X f.unop)
    -- The sections of `pushforwardAlgebra` and `Γ(·, ·)` are definitionally equal but spelled
    -- differently, so neither `rw` nor `simp` can match `Category.assoc` here: both unify at
    -- reducible transparency.  Every reassociation below is therefore an explicit
    -- `congrArg`/`Eq.trans` term, which is checked at default transparency.
    have hM : eY.hom ≫ AY ≫ eZ.inv = MY :=
      ((Category.assoc eY.hom AY eZ.inv).symm.trans
          (congrArg (· ≫ eZ.inv) h.symm)).trans
        (((Category.assoc MY eZ.hom eZ.inv).trans
          (congrArg (MY ≫ ·) eZ.hom_inv_id)).trans (Category.comp_id MY))
    have key : AY ≫ eZ.inv = eY.inv ≫ MY :=
      ((congrArg (eY.inv ≫ ·) hM.symm).trans
        (Iso.inv_hom_id_assoc eY (AY ≫ eZ.inv))).symm
    have inner : (AY ≫ tZ.inv) ≫ tZ.hom ≫ eZ.inv = eY.inv ≫ MY :=
      (Category.assoc AY tZ.inv (tZ.hom ≫ eZ.inv)).trans
        ((congrArg (AY ≫ ·) (Iso.inv_hom_id_assoc tZ eZ.inv)).trans key)
    change (f.unop.hom.left.resLE _ _ (over_preimage_le f.unop.hom U)).appTop ≫
      ((Z.unop.obj.hom ⁻¹ᵁ U).topIso.hom ≫ eZ.inv) =
        ((Y.unop.obj.hom ⁻¹ᵁ U).topIso.hom ≫ eY.inv) ≫ _
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← pushforwardAlgebraMap_app]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((Y.unop.obj.hom ⁻¹ᵁ U).topIso.hom ≫ ·) inner).trans
        (Category.assoc _ _ _).symm))

/-- A cocone of sheaves of rings is colimiting as soon as it is colimiting on the sections over
every affine open, because the affine opens form a basis. -/
noncomputable def isColimit_of_affineSections
    {X : Scheme.{u}} {J : Type*} [Category J]
    {F : J ⥤ TopCat.Sheaf CommRingCat X} (c : Cocone F)
    (hc : ∀ U : X.affineOpens, IsColimit
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (.op U.1)).mapCocone c)) :
    IsColimit c := by
  let B : X.affineOpens → X.Opens := Subtype.val
  have hB : Opens.IsBasis (Set.range B) := by
    simpa only [B, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens
  let R : TopCat.Sheaf CommRingCat X ⥤ ((InducedCategory X.Opens B)ᵒᵖ ⥤ CommRingCat) :=
    sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (inducedFunctor B).op
  have : R.Full := ⟨fun {P Q} f => by
    refine ⟨⟨TopCat.Sheaf.restrictHomEquivHom P.obj Q hB f⟩, ?_⟩
    exact NatTrans.ext <| funext fun U => TopCat.Sheaf.extend_hom_app P.obj Q hB f U.unop⟩
  have : R.Faithful := ⟨fun {P Q} {f g} h => (sheafToPresheaf _ _).map_injective <|
    TopCat.Sheaf.hom_ext P.obj Q hB fun U => congrArg (fun t => t.app (.op U)) h⟩
  exact isColimitOfReflects R (evaluationJointlyReflectsColimits (R.mapCocone c) (hc ·.unop))

/-- An affine-over scheme restricted to the part over an affine open is affine.  Kept as a
separate lemma with explicit binders: this is the one place where `restrictOver` has to be
unfolded, and doing it once here keeps it out of the colimit comparison below. -/
lemma isAffine_restrictOver_obj {X : Scheme.{u}} (U : X.affineOpens) (Y : AffineOver X) :
    IsAffine ((restrictOver U.1).obj ((IsAffineHomOver X).ι.obj Y)) := by
  have : IsAffineHom Y.obj.hom := Y.property
  exact U.2.preimage Y.obj.hom

/-- Global sections turn the opposite of a limit cone of affine schemes into a colimit.  The
restriction functor `H` is an explicit binder rather than a composite, so the comparison of
`(D ⋙ H).op ⋙ Γ` with `D.op ⋙ H.op ⋙ Γ` never unfolds it. -/
noncomputable def isColimitGammaMapCocone {X : Scheme.{u}} {J : Type*} [Category J]
    {D : J ⥤ AffineOver X} (c : Cone D) (H : AffineOver X ⥤ Scheme.{u})
    (h : IsLimit (H.mapCone c)) [PreservesColimit (D ⋙ H).op Scheme.Γ] :
    IsColimit ((H.op ⋙ Scheme.Γ).mapCocone c.op) :=
  isColimitOfPreserves Scheme.Γ h.op

/-- The sections over a single affine open `U`: the limit of the affine schemes over `U` is
computed by global sections, so the algebra sections over `U` form a colimit. -/
noncomputable def isColimitSectionsOverAffine
    (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type*} [Category J] [IsConnected J]
    {D : J ⥤ AffineOver X} (c : Cone D)
    (hc : IsLimit ((IsAffineHomOver X).ι.mapCone c)) (U : X.affineOpens) :
    IsColimit (((E.equivalence X).functor ⋙ (IsQuasicoherentAlgebra X).ι ⋙
      Under.forget X.sheaf ⋙ sheafToPresheaf _ _ ⋙
        (evaluation _ _).obj (.op U.1)).mapCocone c.op) := by
  letI : PreservesLimitsOfShape J (restrictOver U.1) :=
    preservesLimitsOfShape_of_natIso (pullbackRestrictOverIso U.1)
  letI : PreservesColimit (D ⋙ (IsAffineHomOver X).ι ⋙ restrictOver U.1).op Scheme.Γ :=
    @preservesColimit_Γ _ _ (D ⋙ (IsAffineHomOver X).ι ⋙ restrictOver U.1).op
      (fun i => isAffine_restrictOver_obj U (D.obj i.unop))
  have h0 : IsLimit (((IsAffineHomOver X).ι ⋙ restrictOver U.1).mapCone c) :=
    isLimitOfPreserves (restrictOver U.1) hc
  exact IsColimit.mapCoconeEquiv (affineSectionsIso E X U.1)
    (isColimitGammaMapCocone c ((IsAffineHomOver X).ι ⋙ restrictOver U.1) h0)

/-- **The core transport.** A limit cone of schemes affine over `X`, over a connected index
category, becomes a colimit cocone of quasi-coherent algebras under the anti-equivalence of
[Stacks, Tag 01SA]. -/
noncomputable def isColimit_of_isLimit_affineOver
    (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type*} [Category J] [IsConnected J]
    {D : J ⥤ AffineOver X} (c : Cone D)
    (hc : IsLimit ((IsAffineHomOver X).ι.mapCone c)) :
    IsColimit (((E.equivalence X).functor ⋙
      (IsQuasicoherentAlgebra X).ι).mapCocone c.op) :=
  isColimitOfReflects (Under.forget X.sheaf)
    (isColimit_of_affineSections _ (isColimitSectionsOverAffine E X c hc))

/-! ### Surjectivity of the transition maps -/

/-- A morphism of algebra sheaves that is surjective on sections over every affine open is
locally surjective. -/
lemma isSurjective_of_affineSections
    {X : Scheme.{u}} {A B : AlgebraSheaf X} (f : A ⟶ B)
    (hf : ∀ U : X.Opens, IsAffineOpen U →
      Function.Surjective (f.right.hom.app (.op U))) :
    AlgebraSheaf.Hom.IsSurjective f := by
  refine (TopCat.Presheaf.isLocallySurjective_iff f.right.hom).mpr fun U t x hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨V, hVU, hf V hV (B.right.obj.map (homOfLE hVU).op t), hxV⟩

/-- For a closed immersion `f` and an affine open `U`, the map `f.appLE U V e` is surjective
when `V = f ⁻¹ᵁ U`. -/
lemma appLE_surjective_of_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : V = f ⁻¹ᵁ U) (e : V ≤ f ⁻¹ᵁ U) : Function.Surjective (f.appLE U V e) := by
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using f.app_surjective U hU

/-- The algebra map attached to a closed immersion of schemes affine over `X` is locally
surjective. -/
lemma isSurjective_map_of_isClosedImmersion
    (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {Y Z : AffineOver X} (f : Y ⟶ Z) [IsClosedImmersion f.hom.left] :
    AlgebraSheaf.Hom.IsSurjective
      ((IsQuasicoherentAlgebra X).ι.map ((E.equivalence X).functor.map f.op)) := by
  apply isSurjective_of_affineSections
  intro U hU
  let ev := Under.forget X.sheaf ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (.op U)
  let eY := ev.mapIso (E.pushforwardIso X Y)
  let eZ := ev.mapIso (E.pushforwardIso X Z)
  have h := congrArg ev.map (E.pushforwardIso_naturality X f)
  change _ ≫ eY.hom = eZ.hom ≫ _ at h
  have hp : Function.Surjective (ev.map (pushforwardAlgebraMap f.hom)) := by
    change Function.Surjective ((pushforwardAlgebraMap f.hom).right.hom.app (.op U))
    rw [pushforwardAlgebraMap_app]
    have : IsAffineHom Z.obj.hom := Z.property
    apply appLE_surjective_of_eq_preimage _ _ (hU.preimage Z.obj.hom)
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have heq := (Iso.eq_comp_inv eY).mpr h
  change Function.Surjective
    (((IsQuasicoherentAlgebra X).ι.map
      ((E.equivalence X).functor.map f.op)).right.hom.app (.op U))
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso eY.inv).surjective.comp
    (hp.comp (ConcreteCategory.bijective_of_isIso eZ.hom).surjective)

/-! ### Transferring the finiteness conditions across the anti-equivalence -/

/-- Finiteness of an affine morphism is detected by its pushed-forward algebra. -/
lemma pushforwardAlgebra_isFinite_iff
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffineHom f] :
    (pushforwardAlgebra f).IsFinite ↔ IsFinite f := by
  rw [AlgebraicGeometry.isFinite_iff]
  exact ⟨fun h => ⟨inferInstance, h⟩, fun h => h.2⟩

/-- A property of ring maps stable under isomorphisms, holding for the structural maps of `B` on
sections over affine opens, also holds for those of any `A ≅ B`. -/
private lemma structure_map_app_of_iso {S : Scheme.{u}} {A B : AlgebraSheaf S} (e : A ≅ B)
    {P : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    (hP : RingHom.RespectsIso P)
    (hB : ∀ U : S.Opens, IsAffineOpen U → P (B.hom.hom.app (.op U)).hom) :
    ∀ U : S.Opens, IsAffineOpen U → P (A.hom.hom.app (.op U)).hom := by
  intro U hU
  have hcomp : A.hom.hom.app (.op U) ≫ e.hom.right.hom.app (.op U) =
      B.hom.hom.app (.op U) := congrArg (fun f => f.hom.app (.op U)) e.hom.w
  let eU := (sheafToPresheaf (Opens.grothendieckTopology S) CommRingCat ⋙
    (evaluation _ _).obj (.op U)).mapIso ((Under.forget S.sheaf).mapIso e)
  have : IsIso (e.hom.right.hom.app (.op U)) := by
    change IsIso eU.hom
    infer_instance
  have hfin := hB U hU
  rw [← hcomp] at hfin
  exact (hP.cancel_right_isIso
    (A.hom.hom.app (.op U)) (e.hom.right.hom.app (.op U))).mp hfin

/-- Finiteness is invariant under an isomorphism of algebra sheaves. -/
lemma isFinite_of_iso {S : Scheme.{u}} {A B : AlgebraSheaf S}
    (e : A ≅ B) (hB : B.IsFinite) : A.IsFinite :=
  structure_map_app_of_iso e RingHom.finite_respectsIso hB

/-- Finite presentation is invariant under an isomorphism of algebra sheaves. -/
lemma isFinitePresentation_of_iso {S : Scheme.{u}} {A B : AlgebraSheaf S}
    (e : A ≅ B) (hB : B.IsFinitePresentation) : A.IsFinitePresentation :=
  structure_map_app_of_iso e RingHom.finitePresentation_respectsIso hB

/-- The algebra sheaf of an affine morphism of finite presentation is finitely presented. -/
lemma pushforwardAlgebra_isFinitePresentation
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffineHom f] (hf : FinitePresentation f) :
    (pushforwardAlgebra f).IsFinitePresentation := by
  intro U hU
  have : LocallyOfFinitePresentation f := hf.1
  have h := f.finitePresentation_appLE hU (hU.preimage f) le_rfl
  rwa [AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h

/-! ### Tag 086N from Tag 09YY -/

/-- The diagram of quasi-coherent algebras attached to an inverse system of schemes affine over
`X` by the anti-equivalence of [Stacks, Tag 01SA]. -/
noncomputable def transportedDiagram (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type (u + 1)} [Preorder J] (D : Jᵒᵖ ⥤ AffineOver X) : J ⥤ AlgebraSheaf X :=
  (opOpEquivalence J).symm.functor ⋙ D.op ⋙ (E.equivalence X).functor ⋙
    (IsQuasicoherentAlgebra X).ι

/-- The value of `transportedDiagram` at `i` is the quasi-coherent algebra attached to
`D.obj (op i)`. -/
lemma transportedDiagram_obj (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type (u + 1)} [Preorder J] (D : Jᵒᵖ ⥤ AffineOver X) (i : J) :
    (transportedDiagram E X D).obj i =
      (IsQuasicoherentAlgebra X).ι.obj
        ((E.equivalence X).functor.obj (.op (D.obj (.op i)))) :=
  rfl

/-- The image under `transportedDiagram` of `i ≤ j` is the algebra map attached to the
transition map `D.map (homOfLE h).op`. -/
lemma transportedDiagram_map (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type (u + 1)} [Preorder J] (D : Jᵒᵖ ⥤ AffineOver X) {i j : J} (h : i ≤ j) :
    (transportedDiagram E X D).map (homOfLE h) =
      (IsQuasicoherentAlgebra X).ι.map
        ((E.equivalence X).functor.map (D.map (homOfLE h).op).op) :=
  rfl

/-- The cocone on `transportedDiagram` obtained from a cone of the inverse system, with its
vertex transported along an isomorphism. -/
noncomputable def transportedCocone (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type (u + 1)} [Preorder J] {D : Jᵒᵖ ⥤ AffineOver X} (c : Cone D)
    {A : AlgebraSheaf X}
    (i : (IsQuasicoherentAlgebra X).ι.obj ((E.equivalence X).functor.obj (.op c.pt)) ⟶ A)
    [IsIso i] : Cocone (transportedDiagram E X D) :=
  ((((E.equivalence X).functor ⋙ (IsQuasicoherentAlgebra X).ι).mapCocone c.op).whisker
    (opOpEquivalence J).symm.functor).extend i

/-- The vertex of `transportedCocone E X c i` is `A`. -/
lemma transportedCocone_pt (E : AffineAlgebraAntiEquivalence.{u}) (X : Scheme.{u})
    {J : Type (u + 1)} [Preorder J] {D : Jᵒᵖ ⥤ AffineOver X} (c : Cone D)
    {A : AlgebraSheaf X}
    (i : (IsQuasicoherentAlgebra X).ι.obj ((E.equivalence X).functor.obj (.op c.pt)) ⟶ A)
    [IsIso i] : (transportedCocone E X c i).pt = A :=
  rfl

/-- The transported cocone is colimiting.  This is `isColimit_of_isLimit_affineOver` reindexed
along `Jᵒᵖᵒᵖ ≌ J` and transported along the isomorphism of vertices. -/
noncomputable def isColimitTransportedCocone (E : AffineAlgebraAntiEquivalence.{u})
    (X : Scheme.{u}) {J : Type (u + 1)} [Preorder J] [IsConnected Jᵒᵖ]
    {D : Jᵒᵖ ⥤ AffineOver X} (c : Cone D)
    (hcOver : IsLimit ((IsAffineHomOver X).ι.mapCone c)) {A : AlgebraSheaf X}
    (i : (IsQuasicoherentAlgebra X).ι.obj ((E.equivalence X).functor.obj (.op c.pt)) ⟶ A)
    [IsIso i] : IsColimit (transportedCocone E X c i) :=
  show IsColimit
      ((((((E.equivalence X).functor ⋙ (IsQuasicoherentAlgebra X).ι).mapCocone c.op).whisker
        (opOpEquivalence J).symm.functor).extend i)) from
    ((isColimit_of_isLimit_affineOver E X c hcOver).whiskerEquivalence
      (opOpEquivalence J).symm).extendIso i

/-- **[Stacks, Tag 086N], given [Stacks, Tag 09YY].** On a quasi-compact and quasi-separated
scheme, a finite quasi-coherent algebra is a directed colimit of finite and finitely presented
quasi-coherent algebras whose transition maps are surjective, provided every finite morphism
over a quasi-compact and quasi-separated base admits the limit presentation of Tag 09YY.

The unconditional form of this statement is `exists_isColimit_finite_finitePresentation`,
which obtains the limit presentation from `finiteLimitPresentationOfIsFinite`. -/
theorem exists_isColimit_finite_finitePresentation_of_finiteLimitPresentation
    (h09YY : ∀ {Z S : Scheme.{u}} (g : Z ⟶ S), IsFinite g → CompactSpace S →
      QuasiSeparatedSpace S → FiniteLimitPresentation g)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AlgebraSheaf X) (hAqc : A.IsQuasicoherent) (hAfin : A.IsFinite) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      (∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation) ∧
        ∀ i j (h : i ≤ j), AlgebraSheaf.Hom.IsSurjective (F.map (homOfLE h)) := by
  let E := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.{u}
  let e := E.equivalence X
  let a : QuasicoherentAlgebra X := ⟨A, hAqc⟩
  let Y := (e.inverse.obj a).unop
  have : IsAffineHom Y.obj.hom := Y.property
  let eA : A ≅ pushforwardAlgebra Y.obj.hom :=
    (IsQuasicoherentAlgebra X).ι.mapIso (e.counitIso.app a).symm ≪≫
      E.pushforwardIso X Y
  have hpush : (pushforwardAlgebra Y.obj.hom).IsFinite := isFinite_of_iso eA.symm hAfin
  have hYfin : IsFinite Y.obj.hom := (pushforwardAlgebra_isFinite_iff Y.obj.hom).mp hpush
  let P := h09YY Y.obj.hom hYfin ‹CompactSpace X› ‹QuasiSeparatedSpace X›
  let _ : Preorder P.indexType := P.indexPreorder
  have : Nonempty P.indexType := P.indexNonempty
  have : IsDirected P.indexType (· ≤ ·) := P.indexDirected
  have : IsConnected P.indexTypeᵒᵖ := IsCofiltered.isConnected _
  let D : P.indexTypeᵒᵖ ⥤ AffineOver X :=
    (IsAffineHomOver X).lift
      (Over.lift P.diagram P.structureMap)
      (fun i => (P.stageFinite i).toIsAffineHom)
  let p (i : P.indexTypeᵒᵖ) : Y ⟶ D.obj i :=
    ⟨Over.homMk (P.limitCone.app i) (P.compatible i).symm⟩
  have hp {i j : P.indexTypeᵒᵖ} (g : i ⟶ j) : p i ≫ D.map g = p j := by
    ext
    change P.limitCone.app i ≫ P.diagram.map g = P.limitCone.app j
    simpa using (P.limitCone.naturality g).symm
  let c : Cone D := Cone.mk Y
    { app := p
      naturality := fun _ _ g => by simpa using (hp g).symm }
  have hcOver : IsLimit ((IsAffineHomOver X).ι.mapCone c) := by
    change IsLimit (Over.liftCone P.diagram P.structureMap
      (Cone.mk Y.obj.left P.limitCone) Y.obj.hom
      (fun i => (P.compatible i).symm))
    exact Over.isLimitLiftCone P.diagram P.structureMap
      (Cone.mk Y.obj.left P.limitCone) Y.obj.hom
      (fun i => (P.compatible i).symm) P.isLimit
  let i : (IsQuasicoherentAlgebra X).ι.obj ((E.equivalence X).functor.obj (.op c.pt)) ⟶ A :=
    (IsQuasicoherentAlgebra X).ι.map (e.counitIso.app a).hom
  have : IsIso i := inferInstanceAs
    (IsIso ((IsQuasicoherentAlgebra X).ι.map (e.counitIso.app a).hom))
  refine ⟨P.indexType, inferInstance, inferInstance, inferInstance,
    transportedDiagram E X D, (transportedCocone E X c i).ι,
    isColimitTransportedCocone E X c hcOver i, fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact ((E.equivalence X).functor.obj (.op (D.obj (.op k)))).property
  · have : IsAffineHom (D.obj (.op k)).obj.hom := (D.obj (.op k)).property
    exact isFinite_of_iso (E.pushforwardIso X (D.obj (.op k)))
      ((pushforwardAlgebra_isFinite_iff (D.obj (.op k)).obj.hom).mpr (P.stageFinite (.op k)))
  · have : IsAffineHom (D.obj (.op k)).obj.hom := (D.obj (.op k)).property
    exact isFinitePresentation_of_iso (E.pushforwardIso X (D.obj (.op k)))
      (pushforwardAlgebra_isFinitePresentation (D.obj (.op k)).obj.hom
        (P.stageFinitePresentation (.op k)))
  · intro k l h
    rw [transportedDiagram_map]
    have : IsClosedImmersion (D.map (homOfLE h).op).hom.left := P.transitionClosed h
    exact isSurjective_map_of_isClosedImmersion E X (D.map (homOfLE h).op)

/-- **[Stacks, Tag 09YY].** A finite morphism over a quasi-compact and quasi-separated base is
the inverse limit of a directed system of morphisms to that base which are finite and of finite
presentation, with closed immersions as transition maps.

[Stacks, Tag 09ZQ] supplies such a system of morphisms of finite presentation, finiteness of
the stages failing only below some index; [Stacks, Tag 09ZN] produces that index, and the
cofinal tail above it is an initial subcategory, so the restricted system has the same
limit. -/
@[stacks 09YY]
noncomputable def finiteLimitPresentationOfIsFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] : FiniteLimitPresentation f := by
  classical
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace X := by rw [← quasiCompact_iff_compactSpace f]; infer_instance
  choose I hpre hnon hdir D t p hc hcomp hstage hclosed hpclosed using
    exists_isLimit_finitePresentation_closedImmersion f
  letI : Preorder I := hpre
  haveI : Nonempty I := hnon
  haveI : IsDirected I (· ≤ ·) := hdir
  haveI (i : I) : CompactSpace (D.obj (op i)) := (hstage (op i)).2.1
  haveI (i : I) : QuasiSeparatedSpace (D.obj (op i)) := (hstage (op i)).2.2
  haveI (i : I) : LocallyOfFiniteType (t.app (op i)) := by
    have : LocallyOfFinitePresentation (t.app (op i)) := (hstage (op i)).1.1
    infer_instance
  have hev := eventually_isFinite_of_isLimit_of_isIntegral (F := D) (p := t)
    (c := Cone.mk X p) hc f
    (fun i => by simpa using (congrArg (fun n => n.app (op i)) hcomp).symm)
    (haffine := fun h => by
      have : IsClosedImmersion (D.map (homOfLE h).op) := hclosed (g := (homOfLE h).op)
      infer_instance)
    (hfinite := fun h => by
      have : IsClosedImmersion (D.map (homOfLE h).op) := hclosed (g := (homOfLE h).op)
      infer_instance)
  have htail := Filter.eventually_atTop.mp hev
  let i₀ : I := htail.choose
  have hi₀ : ∀ b, i₀ ≤ b → IsFinite (t.app (op b)) := htail.choose_spec
  let J : Type (u + 1) := ULift.{u + 1} (Set.Ici i₀)
  letI : Preorder J := inferInstance
  haveI : Nonempty J := ⟨ULift.up ⟨i₀, le_rfl⟩⟩
  haveI : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) (a.down : I) (b.down : I)
    exact ⟨ULift.up ⟨k, le_trans a.down.2 hak⟩, hak, hbk⟩⟩
  let idx : J → I := fun j => j.down.1
  have hidx : ∀ {a b : J}, a ≤ b → idx a ≤ idx b := fun h => h
  let incl : Jᵒᵖ ⥤ Iᵒᵖ :=
    { obj := fun j => op (idx j.unop)
      map := fun {_ _} g => (homOfLE (hidx (leOfHom g.unop))).op
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  haveI hincl : incl.Initial := by
    refine Functor.initial_of_exists_of_isCofiltered incl (fun d => ?_) (fun {_ c} _ _ => ?_)
    · obtain ⟨k, hdk, hi₀k⟩ := directed_of (· ≤ ·) d.unop i₀
      exact ⟨op (ULift.up ⟨k, hi₀k⟩), ⟨(homOfLE hdk).op⟩⟩
    · exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩
  let D' : Jᵒᵖ ⥤ Scheme.{u} := incl ⋙ D
  let t' : D' ⟶ (Functor.const Jᵒᵖ).obj S := Functor.whiskerLeft incl t
  let p' : (Functor.const Jᵒᵖ).obj X ⟶ D' := Functor.whiskerLeft incl p
  exact
    { indexType := J
      diagram := D'
      structureMap := t'
      limitCone := p'
      compatible := fun j => congrArg (fun n => n.app (op (idx j.unop))) hcomp.symm
      isLimit := (Functor.Initial.isLimitWhiskerEquiv incl (Cone.mk X p)).symm hc
      compactOpenDescends := fun U hU => by
        let j : Jᵒᵖ := op (ULift.up ⟨i₀, le_rfl⟩)
        have : IsClosedImmersion (p'.app j) := hpclosed (incl.obj j)
        obtain ⟨V, hV, hVU⟩ :=
          exists_isCompact_preimage_eq_of_isClosedImmersion (p'.app j) U hU
        exact ⟨j, V, hV, hVU⟩
      stageFinite := fun j => hi₀ _ j.unop.down.2
      stageFinitePresentation := fun j => (hstage (op (idx j.unop))).1
      transitionClosed := fun {_ _} h => hclosed (g := (homOfLE (hidx h)).op) }

/-- **Stacks Project, Tag 086N.** On a quasi-compact and quasi-separated scheme, a finite
quasi-coherent algebra is a directed colimit of finite and finitely presented quasi-coherent
algebras whose transition maps are surjective. -/
@[stacks 086N]
theorem exists_isColimit_finite_finitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (A : AlgebraSheaf X) (hAqc : A.IsQuasicoherent)
    (hAfin : A.IsFinite) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      (∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation) ∧
        ∀ i j (h : i ≤ j), AlgebraSheaf.Hom.IsSurjective (F.map (homOfLE h)) :=
  exists_isColimit_finite_finitePresentation_of_finiteLimitPresentation
    (fun g hg hS hSqs => @finiteLimitPresentationOfIsFinite _ _ g hg hS hSqs) X A hAqc hAfin

end Stacks.FiniteAlgebraLimitPresentation

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FibrewiseCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# An isomorphism on one fibre is an isomorphism over a neighbourhood of the base

Let `X` and `Y` be proper over a Noetherian scheme `S` with `X` flat over `S`, and let
`p : X ⟶ Y` be a morphism over `S` which is an isomorphism on the fibre over a point `s`. Then
`p` becomes an isomorphism after base change to some open neighbourhood of `s`.

## Main results

* `AlgebraicGeometry.exists_isIso_baseChange_of_isIso_fiber`: an isomorphism on the fibre at `s`
  extends to an isomorphism over an open neighbourhood of `s`.

## Implementation notes

Schemes over `S` are objects of `Over S`, and both the fibre at `s` and the restriction over an
open `U` are base changes, taken with `CategoryTheory.Over.pullback` along
`AlgebraicGeometry.Scheme.fromSpecResidueField` and along `U.ι` respectively. Base change along
a composite is compared with iterated base change by
`AlgebraicGeometry.overPullback_map_comp_iff`, and
`AlgebraicGeometry.overPullback_isPullback` identifies the base-changed morphism with a pullback
projection, which is how finiteness, flatness and the fibre rank are transported.

The argument is the source's. Fibrewise isomorphy makes the fibres of `p` singletons, so `p` is
quasi-finite above `s`; as `p` is proper this makes `p` finite over a neighbourhood of `s`
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). Flatness of `p` above `s` is
the fibrewise criterion for flatness
`Stacks.Flatness.isFlatOverBaseAndFiberAt_iff_of_isLocallyNoetherian` applied to the structure
sheaf of `X`: `X` is flat over `S`, and the restriction of `p` to the fibre is an isomorphism,
hence flat. Properness then spreads both conditions to a neighbourhood of `s` in the base
(`AlgebraicGeometry.isOpen_setOf_isFlatAt_of_isLocallyNoetherian` for the flat locus). A finite
flat morphism of locally Noetherian schemes is an isomorphism exactly where its fibre rank is
`1` (`AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq`), the rank is locally constant, and it
is `1` on the fibre over `s`; shrinking the base once more finishes the proof.

Three facts are supplied by name rather than left to instance synthesis. Coherence of the
structure sheaf is needed in the spelling `Stacks.SheafOfModules.IsCoherent`, which is the
predicate the fibrewise criterion takes and which
`Stacks.AlgebraicGeometry.CoherentOfFiniteType.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType`
produces; quasi-coherence is needed with the base sheaf of rings written
`structureSheafRing X.toRingedSpace` rather than `X.ringCatSheaf`, which is
the same sheaf but not at the transparency instance search runs at, so it is crossed by an
explicit type ascription; and `MorphismProperty.RespectsIso` for `AlgebraicGeometry.IsFinite`
and `AlgebraicGeometry.Flat` is `MorphismProperty.IsStableUnderBaseChange.respectsIso`.

For the same reason the base change along `Spec κ(s) ⟶ S` is refactored through
`AlgebraicGeometry.overPullback_map_comp` rather than through the image of an isomorphism under
`CategoryTheory.Over.pullback`: the target of `Spec.map (U.ι.residueFieldMap ⟨s, hs⟩)` is
`Spec κ(U.ι ⟨s, hs⟩)`, not `Spec κ(s)`, so the composite is only definitionally a base change of
the fibre at `s`.

## References

* [Stacks Project, Tag 0G0Q](https://stacks.math.columbia.edu/tag/0G0Q)
* [Stacks Project, Tag 039B](https://stacks.math.columbia.edu/tag/039B)
* [Stacks Project, Tag 0255](https://stacks.math.columbia.edu/tag/0255)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentOfFiniteType
open Stacks.Flatness

universe u

namespace AlgebraicGeometry

/-! ### Base change along a morphism of bases -/

/-- The base change of a morphism over `S` along `q : T ⟶ S`, read as the second projection of
a pullback over the base change of the target. -/
private noncomputable def overPullbackMapArrowIso {S T : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    (q : T ⟶ S) :
    Arrow.mk ((Over.pullback q).map p).left ≅
      Arrow.mk (pullback.snd p.left (pullback.fst Y.hom q)) :=
  Arrow.isoMk (asIso (overPullback_isPullback q X Y p).isoPullback.hom) (Iso.refl _)
    (overPullback_isPullback q X Y p).isoPullback_hom_snd

private lemma isIso_overPullback_map_iff {S T : Scheme.{u}} (q : T ⟶ S) (X Y : Over S)
    (p : X ⟶ Y) :
    IsIso ((Over.pullback q).map p).left ↔
      IsIso (pullback.snd p.left (pullback.fst Y.hom q)) := by
  rw [← (overPullback_isPullback q X Y p).isoPullback_hom_snd]
  exact isIso_comp_left_iff _ _

private lemma isIso_overPullback_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    {P Q : Over C} (k : P ⟶ Q)
    (hk : IsIso ((Over.pullback f).map ((Over.pullback g).map k)).left) :
    IsIso ((Over.pullback (f ≫ g)).map k).left :=
  (overPullback_map_comp_iff (MorphismProperty.isomorphisms Scheme.{u}) g f k).mpr hk

private lemma isIso_overPullback_comp_of_isIso {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    {P Q : Over C} (k : P ⟶ Q)
    (hk : IsIso ((Over.pullback (f ≫ g)).map k).left) :
    IsIso ((Over.pullback f).map ((Over.pullback g).map k)).left :=
  (overPullback_map_comp_iff (MorphismProperty.isomorphisms Scheme.{u}) g f k).mp hk

/-- Base change along an isomorphism of bases reflects being an isomorphism: the two projections
of the pullback squares are themselves isomorphisms. -/
private lemma isIso_of_isIso_overPullback_isIso {A B : Scheme.{u}} (q : A ⟶ B) [IsIso q]
    {P Q : Over B} (k : P ⟶ Q) (hk : IsIso ((Over.pullback q).map k).left) : IsIso k.left :=
  (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme.{u})
    (Arrow.isoMk (asIso (pullback.fst P.hom q)) (asIso (pullback.fst Q.hom q))
      (overPullback_isPullback q P Q k).w)).mp hk

/-- Base change to the residue field of a point of an open subscheme, factored through the open
subscheme. -/
private lemma isIso_overPullback_residueAfterOpen {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    (U : S.Opens) (s : S) (hs : s ∈ U)
    (hp : IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left) :
    IsIso ((Over.pullback (U.toScheme.fromSpecResidueField ⟨s, hs⟩)).map
      ((Over.pullback U.ι).map p)).left := by
  have hpDirect : IsIso ((Over.pullback
      (U.toScheme.fromSpecResidueField ⟨s, hs⟩ ≫ U.ι)).map p).left := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι ⟨s, hs⟩]
    exact overPullback_map_comp (MorphismProperty.isomorphisms Scheme.{u})
      (S.fromSpecResidueField s) (Spec.map (U.ι.residueFieldMap ⟨s, hs⟩)) p hp
  exact isIso_overPullback_comp_of_isIso _ U.ι p hpDirect

/-! ### Consequences of fibrewise isomorphy -/

/-- A morphism over `S` which becomes an isomorphism after base change along `q : B ⟶ S` has
singleton fibres above the image of `B`. -/
private lemma subsingleton_preimage_of_fiber_isIso {S B : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    (q : B ⟶ S) (hp : IsIso ((Over.pullback q).map p).left)
    (y : Y.left) (b : B) (hy : Y.hom y = q b) :
    Subsingleton (p.left ⁻¹' {y}) := by
  let v := pullback.fst Y.hom q
  have hv : IsIso (pullback.snd p.left v) :=
    (isIso_overPullback_map_iff q X Y p).mp hp
  have hinj : Function.Injective (pullback.snd p.left v) :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.forgetToTop.map (pullback.snd p.left v))).injective
  refine ⟨fun x₁ x₂ => Subtype.ext ?_⟩
  obtain ⟨y₁, hy₁⟩ := Scheme.Pullback.exists_preimage_pullback y b hy
  obtain ⟨x₁', hx₁', hx₁''⟩ := Scheme.Pullback.exists_preimage_pullback
    x₁.1 y₁ (by rw [x₁.2, hy₁.1])
  obtain ⟨x₂', hx₂', hx₂''⟩ := Scheme.Pullback.exists_preimage_pullback
    x₂.1 y₁ (by rw [x₂.2, hy₁.1])
  obtain rfl : x₁' = x₂' := hinj (by rw [hx₁'', hx₂''])
  exact hx₁'.symm.trans hx₂'

/-- A proper morphism which is an isomorphism on the fibre at `s` is quasi-finite at every point
above `s`. -/
private lemma quasiFiniteAt_of_isIso_fiber {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    [IsProper p.left] (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left]
    (x : X.left) (hx : X.hom x = s) :
    p.left.QuasiFiniteAt x := by
  have hy : Y.hom (p.left x) = s := by
    rwa [← Scheme.Hom.comp_apply, p.w]
  obtain ⟨b, hb⟩ : s ∈ Set.range (S.fromSpecResidueField s) := by
    rw [Scheme.range_fromSpecResidueField]
    simp
  have hsub : Subsingleton (p.left ⁻¹' {p.left x}) :=
    subsingleton_preimage_of_fiber_isIso p (S.fromSpecResidueField s)
      inferInstance (p.left x) b (hy.trans hb.symm)
  have : Subsingleton (p.left.fiber (p.left x)) :=
    ⟨fun _ _ => (p.left.fiberHomeo _).injective (hsub.elim _ _)⟩
  have hsupp : ({p.left.asFiber x} : Set (p.left.fiber (p.left x))) = Set.univ :=
    Set.eq_univ_of_forall fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, hsupp]
  exact isOpen_univ

/-- An open subset of the source of a proper morphism containing a whole fibre contains the
preimage of an open neighbourhood of that point of the base. -/
private lemma exists_base_open_preimage_le {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (W : X.Opens) (hW : ∀ x : X, f x = s → x ∈ W) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ x : X, f x ∈ U → x ∈ W := by
  let C : Set X := (W : Set X)ᶜ
  have hC : IsClosed C := W.2.isClosed_compl
  let U : S.Opens := ⟨(f '' C)ᶜ, (f.isClosedMap C hC).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · show s ∉ f '' C
    rintro ⟨x, hxC, hxs⟩
    exact hxC (hW x hxs)
  · intro x hxU
    change f x ∉ f '' C at hxU
    by_contra hxW
    exact hxU ⟨x, hxW, rfl⟩

/-- The morphism induced on the fibres over `s` by `f : X ⟶ Y` sits in a pullback square over
`f` and the inclusion of the fibre of `Y`. -/
private lemma fiberHom_isPullback {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    IsPullback ((f ≫ g).fiberι s) (fiberHom f g s) f (g.fiberι s) := by
  have h1 : fiberHom f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f := pullback.lift_fst ..
  have h2 : fiberHom f g s ≫ g.fiberToSpecResidueField s =
      (f ≫ g).fiberToSpecResidueField s := pullback.lift_snd ..
  refine (IsPullback.of_right ?_ h1
    (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).flip).flip
  show IsPullback (fiberHom f g s ≫ g.fiberToSpecResidueField s)
    ((f ≫ g).fiberι s) (S.fromSpecResidueField s) (f ≫ g)
  rw [h2]
  exact (IsPullback.of_hasPullback (f ≫ g) (S.fromSpecResidueField s)).flip

/-- Fibrewise isomorphy of a morphism over `S`, read on the fibre schemes. -/
private lemma isIso_fiberHom_of_overPullback {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left] :
    IsIso (fiberHom p.left Y.hom s) := by
  have hsnd : IsIso (pullback.snd p.left (Y.hom.fiberι s)) :=
    (isIso_overPullback_map_iff (S.fromSpecResidueField s) X Y p).mp inferInstance
  rw [← (fiberHom_isPullback p.left Y.hom s).isoPullback_hom_snd]
  exact (isIso_comp_left_iff _ _).mpr hsnd

/-! ### Flatness above the fibre -/

/-- The stalk of the structure sheaf, read as a module over itself, is nonzero. -/
private alias exists_ne_zero_stalk_unit := exists_ne_zero_unitStalk

/-- **Stacks Project, Tag 0G0Q**, the key local step. With `X` and `Y` proper over a Noetherian
`S`, `X` flat over `S` at `x` and `p` an isomorphism on the fibre at `s`, the morphism `p` is
flat at `x` whenever `x` lies above `s`. -/
private lemma flatAt_of_isIso_fiber {S : Scheme.{u}} [IsNoetherian S] {X Y : Over S} (p : X ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left]
    (x : X.left) (hx : X.hom x = s)
    (hXflat : AlgebraicGeometry.IsFlatAt X.hom.toLRSHom.toShHom x) :
    AlgebraicGeometry.IsFlatAt p.left.toLRSHom.toShHom x := by
  obtain rfl : s = Y.hom (p.left x) := by
    rw [← hx, ← Scheme.Hom.comp_apply, p.w]
  let F : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let f := p.left
  let g := Y.hom
  let fiberMap := fiberHom f g (g (f x))
  let fiberMapR := fiberMap.toLRSHom.toShHom
  have hfg : (f ≫ g) x = g (f x) := rfl
  let sourcePoint : (f ≫ g).fiber (g (f x)) := hfg ▸ (f ≫ g).asFiber x
  let sourceFiberModule :=
    ((Scheme.Modules.pullback ((f ≫ g).fiberι (g (f x)))).obj F)
  have hpull : AlgebraicGeometry.IsFlatOverAt fiberMapR sourceFiberModule sourcePoint := by
    have : IsIso fiberMap := isIso_fiberHom_of_overPullback p (g (f x))
    have hunit : AlgebraicGeometry.IsFlatOverAt fiberMapR
        (SheafOfModules.unit ((f ≫ g).fiber (g (f x))).ringCatSheaf) sourcePoint :=
      (isFlatOverAt_unit_iff_isFlatAt fiberMap sourcePoint).mpr
        (Flat.stalkMap fiberMap sourcePoint)
    exact (isFlatOverAt_iff_of_moduleIso fiberMapR
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ((f ≫ g).fiberι (g (f x))))
      sourcePoint).mpr hunit
  have hbase : Stacks.Flatness.IsFlatOverBaseAndFiberAt f g F x := by
    refine ⟨?_, ?_⟩
    · have hX' : AlgebraicGeometry.IsFlatOverAt X.hom.toLRSHom.toShHom F x :=
        (isFlatOverAt_unit_iff_isFlatAt X.hom x).mpr hXflat
      simpa [f, g, p.w] using hX'
    · show AlgebraicGeometry.IsFlatOverAt fiberMapR sourceFiberModule sourcePoint
      exact hpull
  -- The two module-theoretic hypotheses of the fibrewise criterion are supplied by name: its base
  -- sheaf of rings is written `structureSheafRing X.toRingedSpace`, and instance search does not
  -- identify that with `X.ringCatSheaf`, at which the instances are available.
  have hmid := (@Stacks.Flatness.isFlatOverBaseAndFiberAt_iff_of_isLocallyNoetherian
    X.left Y.left S f g F inferInstance inferInstance inferInstance
    (by exact (inferInstance : SheafOfModules.IsQuasicoherent
      (R := X.left.ringCatSheaf) (SheafOfModules.unit X.left.ringCatSheaf)))
    (by
      exact stacksIsCoherent_of_isQuasicoherent_of_isFiniteType (X := X.left)
        (SheafOfModules.unit X.left.ringCatSheaf))
    x (by exact exists_ne_zero_stalk_unit X.left x)).mp hbase
  simpa [f, F] using (isFlatOverAt_unit_iff_isFlatAt f x).mp hmid.2

/-- The underlying morphism of a morphism between schemes proper over `S` is proper. -/
private lemma isProper_left_of_isProper {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] : IsProper p.left := by
  have : IsProper (p.left ≫ Y.hom) := by
    rw [p.w]
    infer_instance
  exact IsProper.of_comp p.left Y.hom

/-- The source of a proper morphism which is an isomorphism on the fibre at `s` is quasi-finite
over the target above an open neighbourhood of `s`. -/
private lemma exists_base_neighborhood_quasiFinite_on_source {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Over S} (p : X ⟶ Y) [IsProper X.hom] [IsProper Y.hom] (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left] :
    ∃ U : S.Opens, s ∈ U ∧
      ∀ x : X.left, X.hom x ∈ U → p.left.QuasiFiniteAt x := by
  have := isProper_left_of_isProper p
  exact exists_base_open_preimage_le X.hom s p.left.quasiFiniteLocus
    fun x hx => quasiFiniteAt_of_isIso_fiber p s x hx

/-! ### Transport over an open of the base -/

/-- A morphism which is quasi-finite above an open `U` of the base is finite over the preimage
of `U` in the target, when it is proper. -/
private lemma isFinite_restrict_of_quasiFinite_near_source {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (U : S.Opens) (hnear : ∀ x : X, (f ≫ g) x ∈ U → f.QuasiFiniteAt x)
    [IsProper f] :
    IsFinite (f ∣_ (g ⁻¹ᵁ U)) := by
  let V : Y.Opens := g ⁻¹ᵁ U
  have hqf : LocallyQuasiFinite (f ∣_ V) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have hpoint : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := hnear _ x.2
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at hpoint
    simpa [V] using hpoint
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f ∣_ V)

/-- The base change of `f : X ⟶ Y` along the base change of an open `U` of `S` is the
restriction of `f` over the preimage of `U`. -/
private noncomputable def pullbackSndRestrictArrowIso {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (U : S.Opens) :
    Arrow.mk (pullback.snd f (pullback.fst g U.ι)) ≅ Arrow.mk (f ∣_ (g ⁻¹ᵁ U)) := by
  let V : Y.Opens := g ⁻¹ᵁ U
  let eY := pullbackRestrictIsoRestrict g U
  let m := pullback.map f (pullback.fst g U.ι) f V.ι
    (𝟙 _) eY.hom (𝟙 _) (by simp)
      (pullbackRestrictIsoRestrict_hom_ι g U).symm
  have hm : IsIso m :=
    pullback.map_isIso f (pullback.fst g U.ι) f V.ι
      (𝟙 _) eY.hom (𝟙 _) (by simp)
      (pullbackRestrictIsoRestrict_hom_ι g U).symm
  let eX := asIso m ≪≫ pullbackRestrictIsoRestrict f V
  have hcomm : eX.hom ≫ (f ∣_ V) =
      pullback.snd f (pullback.fst g U.ι) ≫ eY.hom := by
    rw [show eX.hom = m ≫ (pullbackRestrictIsoRestrict f V).hom from rfl, Category.assoc,
      pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact pullback.lift_snd ..
  exact Arrow.isoMk eX eY hcomm

/-- A property stable under isomorphisms holding for the restriction of `p.left` over the
preimage of `U` holds for the base change of `p` along `U.ι`. -/
private lemma overPullback_map_of_restrict {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (U : S.Opens) (h : P (p.left ∣_ (Y.hom ⁻¹ᵁ U))) :
    P ((Over.pullback U.ι).map p).left :=
  (MorphismProperty.arrow_mk_iso_iff (P := P) (overPullbackMapArrowIso p U.ι)).mpr
    ((MorphismProperty.arrow_mk_iso_iff (P := P)
      (pullbackSndRestrictArrowIso p.left Y.hom U)).mpr h)

/-- A morphism flat at every point above an open `V` of the target is flat over `V`. -/
private lemma flat_restrict_of_flatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hflat : ∀ x : X, f x ∈ V →
      AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) : Flat (f ∣_ V) := by
  rw [← f.resLE_eq_morphismRestrict (U := V)]
  apply Flat.of_stalkMap
  intro z
  have hf : (f.stalkMap ((f ⁻¹ᵁ V).ι z)).hom.Flat := hflat _ z.2
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.Hom.resLEStalkMap f (U := V) (V := f ⁻¹ᵁ V) le_rfl z)).mpr hf

/-! ### The theorem -/

/-- **Stacks Project, Tag 0G0Q, with flatness only above `s`.** Let `X` and `Y` be proper over a
Noetherian scheme `S` and let `p : X ⟶ Y` be an `S`-morphism which is an isomorphism on the
fibre at `s`. If `X ⟶ S` is flat at every point above `s` — which is all that the flatness
hypothesis of the source is used for — then `p` is an isomorphism after base change to some open
neighbourhood of `s`.

The source's own hypothesis, flatness of `X ⟶ S` everywhere, is the specialization
`AlgebraicGeometry.exists_isIso_baseChange_of_isIso_fiber` below. -/
public theorem exists_isIso_baseChange_of_flatAt_of_isIso_fiber
    {S : Scheme.{u}} [IsNoetherian S] {X Y : Over S} (p : X ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left]
    (hXflat : ∀ x : X.left, X.hom x = s →
      AlgebraicGeometry.IsFlatAt X.hom.toLRSHom.toShHom x) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((Over.pullback U.ι).map p).left := by
  have : MorphismProperty.RespectsIso (@IsFinite) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := isProper_left_of_isProper p
  let W : X.left.Opens := ⟨{x | AlgebraicGeometry.IsFlatAt p.left.toLRSHom.toShHom x},
    AlgebraicGeometry.isOpen_setOf_isFlatAt_of_isLocallyNoetherian p.left⟩
  obtain ⟨Uf, hsUf, hUf⟩ := exists_base_open_preimage_le X.hom s W
    fun x hx => flatAt_of_isIso_fiber p s x hx (hXflat x hx)
  obtain ⟨Uq, hsUq, hUq⟩ := exists_base_neighborhood_quasiFinite_on_source p s
  let U : S.Opens := Uf ⊓ Uq
  have hsU : s ∈ U := ⟨hsUf, hsUq⟩
  have hbaseU : ∀ x : X.left, Y.hom (p.left x) ∈ U → X.hom x ∈ U := fun x hx => by
    rwa [← Scheme.Hom.comp_apply, p.w] at hx
  let pU := (Over.pullback U.ι).map p
  have : IsFinite pU.left :=
    overPullback_map_of_restrict (P := @IsFinite) p U
      (isFinite_restrict_of_quasiFinite_near_source p.left Y.hom U fun x hx =>
        hUq x (hbaseU x (by simpa only [Scheme.Hom.comp_apply] using hx)).2)
  have : Flat pU.left :=
    overPullback_map_of_restrict (P := @Flat) p U
      (flat_restrict_of_flatAt p.left (Y.hom ⁻¹ᵁ U) fun x hx => hUf x (hbaseU x hx).1)
  let YU := (Over.pullback U.ι).obj Y
  let gU := YU.hom
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  have : IsProper gU := by
    dsimp [gU, YU]
    infer_instance
  have : IsLocallyNoetherian YU.left := LocallyOfFiniteType.isLocallyNoetherian gU
  have : LocallyOfFinitePresentation pU.left :=
    (AlgebraicGeometry.finitePresentation_of_finiteType pU.left).1
  let us : U.toScheme := ⟨s, hsU⟩
  have : IsIso ((Over.pullback (U.toScheme.fromSpecResidueField us)).map pU).left :=
    isIso_overPullback_residueAfterOpen p U s hsU inferInstance
  let fiberMapU := fiberHom pU.left gU us
  have : IsIso fiberMapU := isIso_fiberHom_of_overPullback pU us
  let R : YU.left.Opens :=
    ⟨{y | Scheme.Hom.finrank pU.left y = 1},
      (Scheme.Hom.isLocallyConstant_finrank pU.left).isOpen_fiber 1⟩
  obtain ⟨W, husW, hW⟩ := exists_base_open_preimage_le gU us R fun y hy => by
    show Scheme.Hom.finrank pU.left y = 1
    let z := (gU.fiberHomeo us).symm ⟨y, hy⟩
    have hz : gU.fiberι us z = y := gU.fiberι_fiberHomeo_symm us ⟨y, hy⟩
    have hcompat : Scheme.Hom.finrank fiberMapU z = Scheme.Hom.finrank pU.left y := by
      rw [← hz]
      exact Scheme.Hom.finrank_of_isPullback ((pU.left ≫ gU).fiberι us) fiberMapU pU.left
        (gU.fiberι us) (fiberHom_isPullback pU.left gU us) z
    exact hcompat.symm.trans (congrFun (Scheme.Hom.finrank_eq_one_of_isIso fiberMapU) z)
  let fW := pullback.snd pU.left (pullback.fst gU W.ι)
  have hIsoFW : IsIso fW := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext z
    have hbase : gU (pullback.fst gU W.ι z) ∈ W := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact (pullback.snd gU W.ι z).2
    show Scheme.Hom.finrank fW z = 1
    exact (Scheme.Hom.finrank_pullback_snd pU.left (pullback.fst gU W.ι) z).trans
      (hW (pullback.fst gU W.ι z) hbase)
  have hIsoQ : IsIso ((Over.pullback (W.ι ≫ U.ι)).map p).left :=
    isIso_overPullback_comp W.ι U.ι p
      ((MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
        (overPullbackMapArrowIso pU W.ι)).mpr hIsoFW)
  let eBase := U.ι.isoImage W
  have hIsoBaseComp : IsIso ((Over.pullback (eBase.hom ≫ (U.ι ''ᵁ W).ι)).map p).left := by
    rwa [Scheme.Hom.isoImage_hom_ι U.ι W]
  exact ⟨U.ι ''ᵁ W, ⟨us, husW, by simp [us]⟩,
    isIso_of_isIso_overPullback_isIso eBase.hom ((Over.pullback (U.ι ''ᵁ W).ι).map p)
      (isIso_overPullback_comp_of_isIso eBase.hom (U.ι ''ᵁ W).ι p hIsoBaseComp)⟩

/-- **Stacks Project, Tag 0G0Q.** Let `X` and `Y` be proper over a Noetherian scheme `S`, with
`X` flat over `S`. An `S`-morphism `X ⟶ Y` which is an isomorphism on the fibre at `s` is an
isomorphism after base change to some open neighbourhood of `s`. -/
@[stacks 0G0Q, ega "III 4.6.7" "(ii)"]
public theorem exists_isIso_baseChange_of_isIso_fiber
    {S : Scheme.{u}} [IsNoetherian S] {X Y : Over S} (p : X ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] [Flat X.hom] (s : S)
    [IsIso ((Over.pullback (S.fromSpecResidueField s)).map p).left] :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((Over.pullback U.ι).map p).left :=
  exists_isIso_baseChange_of_flatAt_of_isIso_fiber p s fun x _ => Flat.stalkMap X.hom x

end AlgebraicGeometry

end

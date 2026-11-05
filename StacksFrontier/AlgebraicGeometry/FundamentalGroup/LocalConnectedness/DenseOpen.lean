module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrum
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData

/-!
# Extending morphisms between finite étale covers across a dense open

Let `U` be a dense open subscheme of a scheme `X` whose underlying space is Noetherian, and
suppose that for every point `x` of `X` outside `U` the punctured spectrum of a strict
henselization of the local ring `𝒪_{X, x}` is connected.  Then base change of finite étale
covers along `U ⟶ X` is fully faithful: a morphism between the restrictions to `U` of two
finite étale covers of `X` comes from a unique morphism over `X`.

## Main results

* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace` — full
  faithfulness of base change to a dense open.
* `AlgebraicGeometry.exists_opens_extension_of_connected_puncturedSpectrum` — a morphism of
  covers defined over a retrocompact open `V` extends over an open neighbourhood of `V` together
  with one chosen point outside it.
* `AlgebraicGeometry.IsConnectedPuncturedStrictHenselization` — the local hypothesis, that the
  punctured spectrum of every strict henselization of a local ring is connected.
* `AlgebraicGeometry.nonempty_fullyFaithful_puncturedSpectrum_of_connected` — that hypothesis
  gives full faithfulness of base change to the punctured spectrum.
* `AlgebraicGeometry.spread_finiteEtale_hom_from_gluingData` — a compatible pair of morphisms on
  an open and on a local scheme comes from a morphism over a neighbourhood.

## References

* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0BQ5](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open IsLocalRing
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-! ### Comparison of base changes to nested opens -/

/-- The comparison morphism between the base changes of `f : Y ⟶ S` to two nested opens of the
base: it is the identity on the `Y`-coordinate and the inclusion on the base coordinate. -/
noncomputable def openPullbackMap {S Y : Scheme.{u}} (f : Y ⟶ S)
    {U V : S.Opens} (h : U ≤ V) : pullback f U.ι ⟶ pullback f V.ι :=
  pullback.lift (pullback.fst f U.ι)
    (pullback.snd f U.ι ≫ S.homOfLE h) (by
      rw [Category.assoc, S.homOfLE_ι]
      exact pullback.condition)

/-- The comparison morphism between base changes to nested opens is the identity on the
`Y`-coordinate. -/
theorem openPullbackMap_fst {S Y : Scheme.{u}} (f : Y ⟶ S)
    {U V : S.Opens} (h : U ≤ V) :
    openPullbackMap f h ≫ pullback.fst f V.ι = pullback.fst f U.ι :=
  pullback.lift_fst _ _ _

/-- On the base coordinate the comparison morphism between base changes to nested opens is the
inclusion of the opens. -/
theorem openPullbackMap_snd {S Y : Scheme.{u}} (f : Y ⟶ S)
    {U V : S.Opens} (h : U ≤ V) :
    openPullbackMap f h ≫ pullback.snd f V.ι = pullback.snd f U.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

/-- The comparison morphisms between base changes to nested opens compose. -/
theorem openPullbackMap_comp {S Y : Scheme.{u}} (f : Y ⟶ S)
    {U V W : S.Opens} (h : U ≤ V) (k : V ≤ W) :
    openPullbackMap f h ≫ openPullbackMap f k = openPullbackMap f (h.trans k) := by
  apply pullback.hom_ext
  · rw [Category.assoc, openPullbackMap_fst, openPullbackMap_fst, openPullbackMap_fst]
  · rw [Category.assoc, openPullbackMap_snd, ← Category.assoc, openPullbackMap_snd,
      Category.assoc, S.homOfLE_homOfLE, openPullbackMap_snd]

/-- The comparison morphism for the inclusion of an open into itself is the identity. -/
theorem openPullbackMap_refl {S Y : Scheme.{u}} (f : Y ⟶ S)
    (U : S.Opens) : openPullbackMap f (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [openPullbackMap_fst, Category.id_comp]
  · rw [openPullbackMap_snd, Category.id_comp, S.homOfLE_rfl, Category.comp_id]

/-- The morphism of `T`-schemes underlying a morphism between the base changes along `g : T ⟶ S`
of two finite étale covers of `S`: the same map of schemes, with its target presented as an
object of the slice category over `T` rather than as a finite étale cover. -/
noncomputable def overHomOfFiniteEtaleBaseChange {S T : Scheme.{u}} (g : T ⟶ S)
    {Y Z : FiniteEtaleOver S}
    (φ : (finiteEtaleBaseChange g).obj Y ⟶ (finiteEtaleBaseChange g).obj Z) :
    (Over.pullback g).obj (Over.mk Y.hom) ⟶ (Over.pullback g).obj (Over.mk Z.hom) :=
  Over.homMk φ.left (MorphismProperty.Over.w φ)

/-! ### Full faithfulness over a punctured local spectrum -/

/-- **The local connectedness hypothesis.** The punctured spectrum of every strict henselization
of the local ring `R` is connected.

A strict henselization is taken in the sense of
`Stacks.StrictHenselization.IsStrictHenselization`, relative to an arbitrary separable algebraic
closure of the residue field of `R`; since a strict henselization is unique up to isomorphism,
quantifying over all of them is no stronger than asserting the condition for one. -/
def IsConnectedPuncturedStrictHenselization (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (κsep : Type u) [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
    [IsSepClosure (maximalIdeal R).ResidueField κsep]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh],
    Stacks.StrictHenselization.IsStrictHenselization R κsep Rsh →
    _root_.IsConnected ({closedPoint Rsh}ᶜ : Set (PrimeSpectrum Rsh))

/-- Base change of finite étale covers to the punctured spectrum of a local ring `R` is fully
faithful as soon as the punctured spectrum of every strict henselization of `R` is connected. -/
theorem nonempty_fullyFaithful_puncturedSpectrum_of_connected
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hconn : IsConnectedPuncturedStrictHenselization R) :
    Nonempty (finiteEtaleBaseChange (puncturedSpectrum R).ι).FullyFaithful := by
  obtain ⟨Rsh, _, _, _, ⟨hsh⟩⟩ :=
    Stacks.StrictHenselization.exists_isStrictHenselization R
      (SeparableClosure (maximalIdeal R).ResidueField)
  exact fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum R
    (SeparableClosure (maximalIdeal R).ResidueField) Rsh hsh
    (hconn (SeparableClosure (maximalIdeal R).ResidueField) Rsh hsh)

/-! ### Neighbourhood models attached to a finite étale cover -/

/-- The natural-transformation form of `AlgebraicGeometry.GlueingNearPoint.canonicalOverlapIso`:
restricting a scheme over `S` first to `U` and then to the punctured local scheme at `x` agrees
with restricting it first to `Spec 𝒪_{S, x}` and then to the punctured local scheme. -/
noncomputable def canonicalOverlapComparisonIso
    (S : Scheme.{u}) (U : S.Opens) (x : S) :
    Over.pullback U.ι ⋙ Over.pullback (S.fromSpecStalk x ∣_ U) ≅
      Over.pullback (S.fromSpecStalk x) ⋙
        Over.pullback (((S.fromSpecStalk x) ⁻¹ᵁ U).ι) :=
  (Over.pullbackComp (S.fromSpecStalk x ∣_ U) U.ι).symm ≪≫
    eqToIso (congrArg (fun f ↦ Over.pullback f)
      (morphismRestrict_ι (S.fromSpecStalk x) U)) ≪≫
    Over.pullbackComp (((S.fromSpecStalk x) ⁻¹ᵁ U).ι) (S.fromSpecStalk x)

/-- A finite étale cover of `S`, viewed as a scheme of finite presentation over the open
neighbourhood `⊤` of `U ∪ {x}`. -/
noncomputable def neighborhoodModelOfFiniteEtale
    {S : Scheme.{u}} (U : S.Opens) (x : S)
    (Y : FiniteEtaleOver S) : FinitePresentationNeighborhoodModel S U x where
  neighborhood := ⟨⊤, le_top, by simp⟩
  source := Y.left
  hom := Y.hom ≫ S.topIso.inv
  finitePresentation := by
    have hfp := finitePresentation_of_finiteEtale Y
    let : LocallyOfFinitePresentation Y.hom := hfp.1
    let : QuasiCompact Y.hom := hfp.2.1
    let : QuasiSeparated Y.hom := hfp.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The restriction of a neighbourhood model to a smaller neighbourhood, by base change. -/
noncomputable abbrev restrictNeighborhoodModel
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) (V : S.Opens)
    (hUV : U ≤ V) (hsV : s ∈ V) (hVX : V ≤ X.neighborhood.V) :
    FinitePresentationNeighborhoodModel S U s where
  neighborhood := ⟨V, hUV, hsV⟩
  source := pullback X.hom (S.homOfLE hVX)
  hom := pullback.snd X.hom (S.homOfLE hVX)
  finitePresentation := by
    let : LocallyOfFinitePresentation X.hom := X.finitePresentation.1
    let : QuasiCompact X.hom := X.finitePresentation.2.1
    let : QuasiSeparated X.hom := X.finitePresentation.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The structural morphism from the restriction of a neighbourhood model to the model. -/
noncomputable abbrev restrictNeighborhoodModelι
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) (V : S.Opens)
    (hUV : U ≤ V) (hsV : s ∈ V) (hVX : V ≤ X.neighborhood.V) :
    FinitePresentationNeighborhoodModel.Hom
      (restrictNeighborhoodModel X V hUV hsV hVX) X :=
  ⟨hVX, pullback.fst X.hom (S.homOfLE hVX), pullback.condition⟩

/-- The structural morphism out of a restricted neighbourhood model is a restriction
morphism. -/
theorem restrictNeighborhoodModelι_mem
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) (V : S.Opens)
    (hUV : U ≤ V) (hsV : s ∈ V) (hVX : V ≤ X.neighborhood.V) :
    FinitePresentationNeighborhoodModel.restrictionMorphisms
      (restrictNeighborhoodModelι X V hUV hsV hVX) := by
  show IsPullback (pullback.fst X.hom (S.homOfLE hVX))
    (pullback.snd X.hom (S.homOfLE hVX)) X.hom (S.homOfLE hVX)
  exact IsPullback.of_isLimit (c := PullbackCone.mk
    (pullback.fst X.hom (S.homOfLE hVX))
    (pullback.snd X.hom (S.homOfLE hVX)) (pullback.condition))
      (pullbackIsPullback X.hom (S.homOfLE hVX))

/-- Restriction morphisms of neighbourhood models admit a calculus of right fractions: two
models can be restricted to the intersection of their neighbourhoods, and a morphism into a
restriction is determined by its composite with the restriction morphism, which is a
monomorphism. -/
theorem restrictionMorphisms_hasRightCalculusOfFractions
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    CategoryTheory.MorphismProperty.HasRightCalculusOfFractions
      (FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s)) := by
  classical
  let W := FinitePresentationNeighborhoodModel.restrictionMorphisms
    (S := S) (U := U) (s := s)
  have hmult : W.IsMultiplicative := by
    refine {
      toContainsIdentities := ⟨?_⟩
      toIsStableUnderComposition := ⟨?_⟩ }
    · intro X
      show IsPullback (𝟙 X.source) X.hom X.hom (S.homOfLE le_rfl)
      simpa using (IsPullback.of_id_fst (f := X.hom))
    · intro X Y Z f g hf hg
      show IsPullback (f.left ≫ g.left) X.hom Z.hom
        (S.homOfLE (f.base_le.trans g.base_le))
      have h₁ : IsPullback f.left X.hom Y.hom (S.homOfLE f.base_le) := hf
      have h₂ : IsPullback g.left Y.hom Z.hom (S.homOfLE g.base_le) := hg
      simpa only [S.homOfLE_homOfLE] using h₁.paste_horiz h₂
  let := hmult
  refine {
    exists_rightFraction := ?_
    ext := ?_ }
  · intro X Y φ
    let Z := φ.Y'
    let f := φ.f
    let w := φ.s
    have hw : W w := φ.hs
    change IsPullback w.left Y.hom Z.hom (S.homOfLE w.base_le) at hw
    let V := X.neighborhood.V ⊓ Y.neighborhood.V
    have hUV : U ≤ V := le_inf X.neighborhood.le_V Y.neighborhood.le_V
    have hsV : s ∈ V := ⟨X.neighborhood.mem_V, Y.neighborhood.mem_V⟩
    let P := restrictNeighborhoodModel X V hUV hsV inf_le_left
    let p := restrictNeighborhoodModelι X V hUV hsV inf_le_left
    have hp : W p := restrictNeighborhoodModelι_mem X V hUV hsV inf_le_left
    let u : P.source ⟶ Z.source :=
      pullback.fst X.hom (S.homOfLE (inf_le_left : V ≤ X.neighborhood.V)) ≫ f.left
    let v : P.source ⟶ Y.neighborhood.V.toScheme := P.hom ≫
      S.homOfLE (inf_le_right : V ≤ Y.neighborhood.V)
    have huv : u ≫ Z.hom = v ≫ S.homOfLE w.base_le := by
      have hpull : pullback.fst X.hom
          (S.homOfLE (inf_le_left : V ≤ X.neighborhood.V)) ≫ X.hom =
          P.hom ≫ S.homOfLE (inf_le_left : V ≤ X.neighborhood.V) := by
        dsimp [P, restrictNeighborhoodModel]
        exact pullback.condition
      calc
        u ≫ Z.hom = pullback.fst X.hom
            (S.homOfLE (inf_le_left : V ≤ X.neighborhood.V)) ≫
              (f.left ≫ Z.hom) := by simp [u, Category.assoc]
        _ = pullback.fst X.hom
            (S.homOfLE (inf_le_left : V ≤ X.neighborhood.V)) ≫
              (X.hom ≫ S.homOfLE f.base_le) := by rw [f.w]
        _ = P.hom ≫ S.homOfLE (inf_le_left : V ≤ X.neighborhood.V) ≫
              S.homOfLE f.base_le := by
          rw [← Category.assoc, hpull]
          simp [Category.assoc]
        _ = P.hom ≫ S.homOfLE (inf_le_right : V ≤ Y.neighborhood.V) ≫
              S.homOfLE w.base_le := by rw [S.homOfLE_homOfLE, S.homOfLE_homOfLE]
        _ = v ≫ S.homOfLE w.base_le := by simp [v, Category.assoc]
    let qleft := hw.lift u v huv
    let q : FinitePresentationNeighborhoodModel.Hom P Y :=
      ⟨inf_le_right, qleft, hw.lift_snd u v huv⟩
    have hcomm : p.left ≫ f.left = q.left ≫ w.left := by
      show pullback.fst X.hom (S.homOfLE inf_le_left) ≫ f.left =
        qleft ≫ w.left
      exact (hw.lift_fst u v huv).symm
    exact ⟨⟨p, hp, q⟩, FinitePresentationNeighborhoodModel.Hom.ext _ _ hcomm⟩
  · intro X Y Y' f g w hw heq
    change IsPullback w.left Y.hom Y'.hom (S.homOfLE w.base_le) at hw
    have : Mono w.left := hw.mono_fst_of_mono
    have hfg : f.left ≫ w.left = g.left ≫ w.left :=
      congrArg (fun k : FinitePresentationNeighborhoodModel.Hom X Y' => k.left) heq
    obtain rfl : f = g :=
      FinitePresentationNeighborhoodModel.Hom.ext f g ((cancel_mono w.left).mp hfg)
    exact ⟨X, 𝟙 _, W.id_mem X, by simp⟩

/-- A morphism in the germ category is represented by an actual map after shrinking the
neighbourhood of its source, the target being restricted to the same open. -/
theorem localization_morphism_has_neighborhood_representative
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    {X Y : FinitePresentationNeighborhoodModel S U s}
    (g : (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q.obj X ⟶
        (FinitePresentationNeighborhoodModel.restrictionMorphisms
          (S := S) (U := U) (s := s)).Q.obj Y) :
    ∃ (Z : FinitePresentationNeighborhoodModel S U s)
      (w : FinitePresentationNeighborhoodModel.Hom Z X)
      (hw : FinitePresentationNeighborhoodModel.restrictionMorphisms w)
      (f : FinitePresentationNeighborhoodModel.Hom Z Y)
      (Y' : FinitePresentationNeighborhoodModel S U s)
      (r : FinitePresentationNeighborhoodModel.Hom Y' Y)
      (_hr : FinitePresentationNeighborhoodModel.restrictionMorphisms r)
      (f' : FinitePresentationNeighborhoodModel.Hom Z Y'),
      Y' = restrictNeighborhoodModel Y Z.neighborhood.V
        Z.neighborhood.le_V Z.neighborhood.mem_V f.base_le ∧
      f'.left ≫ r.left = f.left ∧
      g = (Localization.Construction.wIso (W :=
        FinitePresentationNeighborhoodModel.restrictionMorphisms
          (S := S) (U := U) (s := s)) w hw).inv ≫
        (FinitePresentationNeighborhoodModel.restrictionMorphisms
          (S := S) (U := U) (s := s)).Q.map f := by
  let W := FinitePresentationNeighborhoodModel.restrictionMorphisms
    (S := S) (U := U) (s := s)
  let : W.HasRightCalculusOfFractions :=
    restrictionMorphisms_hasRightCalculusOfFractions S U s
  let Q := W.Q
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q W g
  let Z := φ.X'
  let w : FinitePresentationNeighborhoodModel.Hom Z X := φ.s
  let f : FinitePresentationNeighborhoodModel.Hom Z Y := φ.f
  have hw : W w := φ.hs
  let Y' := restrictNeighborhoodModel Y Z.neighborhood.V
    Z.neighborhood.le_V Z.neighborhood.mem_V f.base_le
  let r := restrictNeighborhoodModelι Y Z.neighborhood.V
    Z.neighborhood.le_V Z.neighborhood.mem_V f.base_le
  have hr : W r := restrictNeighborhoodModelι_mem Y Z.neighborhood.V
    Z.neighborhood.le_V Z.neighborhood.mem_V f.base_le
  let f' : FinitePresentationNeighborhoodModel.Hom Z Y' := by
    refine ⟨le_rfl, pullback.lift f.left Z.hom f.w, ?_⟩
    show pullback.lift f.left Z.hom f.w ≫ Y'.hom =
        Z.hom ≫ S.homOfLE (le_rfl : Z.neighborhood.V ≤ Z.neighborhood.V)
    dsimp [Y', restrictNeighborhoodModel]
    rw [pullback.lift_snd]
    simp
  have hf_left : f'.left ≫ r.left = f.left := by
    show pullback.lift f.left Z.hom f.w ≫
      pullback.fst Y.hom (S.homOfLE f.base_le) = f.left
    exact pullback.lift_fst f.left Z.hom f.w
  refine ⟨Z, w, hw, f, Y', r, hr, f', rfl, hf_left, ?_⟩
  have hmap : g = inv (Q.map w) ≫ Q.map f := by
    simpa only [MorphismProperty.RightFraction.map] using hφ
  have : IsIso (Q.map w) :=
    (Localization.Construction.wIso (W := W) w hw).isIso_hom
  have hinv : inv (Q.map w) =
      (Localization.Construction.wIso (W := W) w hw).inv :=
    (cancel_mono (Q.map w)).mp ((IsIso.inv_hom_id (Q.map w)).trans
      (Iso.inv_hom_id (Localization.Construction.wIso (W := W) w hw)).symm)
  rwa [hinv] at hmap

/-! ### Transport of commutative squares along isomorphisms -/

/-- Inverting both verticals of a commutative square turns it into the commutative square with
the two horizontals exchanged. -/
private lemma inverse_square_of_isos {C : Type*} [Category C]
    {A B C₁ D : C} (i : A ≅ B) (j : C₁ ≅ D)
    (f : B ⟶ D) (g : A ⟶ C₁) (h : i.hom ≫ f = g ≫ j.hom) :
    i.inv ≫ g = f ≫ j.inv := by
  calc
    i.inv ≫ g = i.inv ≫ (g ≫ j.hom) ≫ j.inv := by simp [Category.assoc]
    _ = i.inv ≫ (i.hom ≫ f) ≫ j.inv := by rw [h]
    _ = f ≫ j.inv := by simp [Category.assoc]

/-- Conjugating a commutative square by four isomorphisms, two of which intertwine the
verticals, gives a commutative square between the conjugated horizontals. -/
private lemma conjugate_commutative_square
    {C : Type*} [Category C] {A B A' B' X Y X' Y' : C}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (d : A ⟶ A') (e : B ⟶ B') (c : X ⟶ X') (k : Y ⟶ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (ha : a.hom ≫ c = d ≫ a'.hom) (hb : b.hom ≫ k = e ≫ b'.hom)
    (hfg : f ≫ k = c ≫ g) :
    (a.hom ≫ f ≫ b.inv) ≫ e = d ≫ (a'.hom ≫ g ≫ b'.inv) := by
  have hi := inverse_square_of_isos b b' k e hb
  simp only [Category.assoc]
  rw [hi, ← Category.assoc f, hfg, Category.assoc,
    ← Category.assoc a.hom c, ha]
  simp only [Category.assoc]

/-- The conjugation of a commutative square whose two columns are the images of a pair of
isomorphisms under two functors into a common category, stated with each conjugated horizontal
presented as the image of a single composite. -/
private lemma functor_conjugate_square
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    (P : C ⥤ D) (Q : C' ⥤ D)
    {A X B Y : C} {A' X' B' Y' : C'}
    (aY : A ≅ X) (aZ : B ≅ Y) (bY : A' ≅ X') (bZ : B' ≅ Y')
    (d : P.obj A ⟶ Q.obj A') (e : P.obj B ⟶ Q.obj B')
    (c : P.obj X ⟶ Q.obj X') (k : P.obj Y ⟶ Q.obj Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (ha : P.map aY.hom ≫ c = d ≫ Q.map bY.hom)
    (hb : P.map aZ.hom ≫ k = e ≫ Q.map bZ.hom)
    (hfg : P.map f ≫ k = c ≫ Q.map g) :
    P.map (aY.hom ≫ f ≫ aZ.inv) ≫ e = d ≫ Q.map (bY.hom ≫ g ≫ bZ.inv) := by
  simp only [Functor.map_comp]
  exact conjugate_commutative_square (P.mapIso aY) (P.mapIso aZ) (Q.mapIso bY) (Q.mapIso bZ)
    d e c k (P.map f) (Q.map g) ha hb hfg

/-- A factorisation statement transported along three isomorphisms: if `w` composed with the
conjugate of `k` is `f`, then `w'` composed with `k` is `f'`. -/
private lemma conjugate_eq_of_commutative_squares
    {C : Type*} [Category C] {A B D A' B' D' : C}
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D')
    (w : A ⟶ B) (f : A ⟶ D) (w' : A' ⟶ B') (f' : A' ⟶ D')
    (k : B' ⟶ D')
    (hw : w ≫ b.hom = a.hom ≫ w') (hf : f ≫ d.hom = a.hom ≫ f')
    (h : w ≫ (b.hom ≫ k ≫ d.inv) = f) : w' ≫ k = f' := by
  apply (cancel_epi a.hom).mp
  calc
    a.hom ≫ w' ≫ k = (w ≫ b.hom) ≫ k := by rw [hw, Category.assoc]
    _ = (w ≫ (b.hom ≫ k ≫ d.inv)) ≫ d.hom := by simp [Category.assoc]
    _ = a.hom ≫ f' := by rw [h, hf]

/-! ### Spreading a compatible pair of morphisms out to a neighbourhood -/

/-- Compatible maps between the restrictions of two finite étale covers to `U` and to the local
scheme at a point `x ∉ U` come from a map defined over an open neighbourhood `V` of `U ∪ {x}`,
out of a model that the morphism `w` exhibits as the base change of the first cover to `V`. -/
lemma spread_finiteEtale_hom_from_gluingData
    (S : Scheme.{u}) (U : S.Opens) (x : S)
    (hx : x ∉ U) (hU : IsRetrocompact (U : Set S))
    (Y Z : FiniteEtaleOver S)
    (fU : (finiteEtaleBaseChange U.ι).obj Y ⟶ (finiteEtaleBaseChange U.ι).obj Z)
    (fA : (finiteEtaleBaseChange (S.fromSpecStalk x)).obj Y ⟶
      (finiteEtaleBaseChange (S.fromSpecStalk x)).obj Z)
    (hcompat :
      (Over.pullback ((S.fromSpecStalk x) ∣_ U)).map
          (overHomOfFiniteEtaleBaseChange U.ι fU) ≫
        (canonicalOverlapIso S U x (Over.mk Z.hom)).hom =
      (canonicalOverlapIso S U x (Over.mk Y.hom)).hom ≫
      (Over.pullback (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).map
          (overHomOfFiniteEtaleBaseChange (S.fromSpecStalk x) fA)) :
    ∃ (V : S.Opens), U ≤ V ∧ x ∈ V ∧
      ∃ (T : Over S) (p : T.left ⟶ V.toScheme)
        (w : T ⟶ Over.mk Y.hom) (f : T ⟶ Over.mk Z.hom),
        IsPullback w.left p Y.hom V.ι ∧
        (Over.pullback U.ι).map w ≫ overHomOfFiniteEtaleBaseChange U.ι fU =
          (Over.pullback U.ι).map f := by
  classical
  let W := FinitePresentationNeighborhoodModel.restrictionMorphisms
    (S := S) (U := U) (s := x)
  let Q := W.Q
  obtain ⟨e, a, b, hc⟩ := glueingEquivalenceNearPoint S U x hx hU
  let MY := neighborhoodModelOfFiniteEtale U x Y
  let MZ := neighborhoodModelOfFiniteEtale U x Z
  let DY := (Q ⋙ e.functor).obj MY
  let DZ := (Q ⋙ e.functor).obj MZ
  let fUo := overHomOfFiniteEtaleBaseChange U.ι fU
  let fAo := overHomOfFiniteEtaleBaseChange (S.fromSpecStalk x) fA
  let i (D : FiniteEtaleOver S) :
      (neighborhoodModelToAmbient S U x).obj (neighborhoodModelOfFiniteEtale U x D) ≅
        Over.mk D.hom := by
    refine Over.isoMk (Iso.refl D.left) ?_
    dsimp [neighborhoodModelOfFiniteEtale, neighborhoodModelToAmbient]
    have htop : S.topIso.inv ≫ (⊤ : S.Opens).ι = 𝟙 S := Scheme.toIso_inv_ι S
    calc
      𝟙 D.left ≫ D.hom = D.hom := Category.id_comp _
      _ = (D.hom ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι := by
        rw [Category.assoc, htop]
        exact (Category.comp_id D.hom).symm
  let aa (D : FiniteEtaleOver S) :=
    (a.app (neighborhoodModelOfFiniteEtale U x D)) ≪≫ (Over.pullback U.ι).mapIso (i D)
  let bb (D : FiniteEtaleOver S) :=
    (b.app (neighborhoodModelOfFiniteEtale U x D)) ≪≫
      (Over.pullback (S.fromSpecStalk x)).mapIso (i D)
  let aY := aa Y
  let aZ := aa Z
  let bY := bb Y
  let bZ := bb Z
  let fOpen : DY.1.left ⟶ DZ.1.left :=
    ObjectProperty.homMk (aY.hom ≫ fUo ≫ aZ.inv)
  let fLocal : DY.1.right ⟶ DZ.1.right :=
    ObjectProperty.homMk (bY.hom ≫ fAo ≫ bZ.inv)
  have hsq :
      (restrictOpenToPuncturedLocal S U x).map fOpen ≫ DZ.1.hom =
        DY.1.hom ≫ (restrictLocalToPuncturedLocal S U x).map fLocal := by
    apply ObjectProperty.hom_ext
    show (Over.pullback (S.fromSpecStalk x ∣_ U)).map
        (aY.hom ≫ fUo ≫ aZ.inv) ≫ DZ.1.hom.hom =
      DY.1.hom.hom ≫ (Over.pullback ((S.fromSpecStalk x ⁻¹ᵁ U).ι)).map
        (bY.hom ≫ fAo ≫ bZ.inv)
    have hside : ∀ D : FiniteEtaleOver S,
        (Over.pullback (S.fromSpecStalk x ∣_ U)).map (aa D).hom ≫
            (canonicalOverlapIso S U x (Over.mk D.hom)).hom =
          ((Q ⋙ e.functor).obj (neighborhoodModelOfFiniteEtale U x D)).1.hom.hom ≫
            (Over.pullback ((S.fromSpecStalk x ⁻¹ᵁ U).ι)).map (bb D).hom := by
      intro D
      have hD := hc (neighborhoodModelOfFiniteEtale U x D)
      dsimp [W, Q, overlapComparisonCompatible] at hD
      have hcan :
          (Over.pullback (S.fromSpecStalk x ∣_ U)).map
              ((Over.pullback U.ι).map (i D).hom) ≫
            (canonicalOverlapIso S U x (Over.mk D.hom)).hom =
          (canonicalOverlapIso S U x
            ((neighborhoodModelToAmbient S U x).obj
              (neighborhoodModelOfFiniteEtale U x D))).hom ≫
            (Over.pullback ((S.fromSpecStalk x ⁻¹ᵁ U).ι)).map
              ((Over.pullback (S.fromSpecStalk x)).map (i D).hom) := by
        simpa [canonicalOverlapComparisonIso, canonicalOverlapIso] using
          (canonicalOverlapComparisonIso S U x).hom.naturality (i D).hom
      dsimp [aa, bb]
      rw [Functor.map_comp, Category.assoc, hcan, ← Category.assoc, hD]
      erw [Category.assoc, ← Functor.map_comp]
      rfl
    exact functor_conjugate_square (Over.pullback (S.fromSpecStalk x ∣_ U))
      (Over.pullback ((S.fromSpecStalk x ⁻¹ᵁ U).ι)) aY aZ bY bZ
      DY.1.hom.hom DZ.1.hom.hom
      (canonicalOverlapIso S U x (Over.mk Y.hom)).hom
      (canonicalOverlapIso S U x (Over.mk Z.hom)).hom
      fUo fAo (hside Y) (hside Z) hcompat
  let dHom : DY ⟶ DZ := ⟨⟨fOpen, fLocal, hsq⟩⟩
  let g : Q.obj MY ⟶ Q.obj MZ := by
    let : e.functor.Full := inferInstance
    exact e.functor.preimage dHom
  have hmap : e.functor.map g = dHom := e.functor.map_preimage dHom
  obtain ⟨M, w, hw, f, _, _, _, _, _, _, hg⟩ :=
    localization_morphism_has_neighborhood_representative S U x g
  have hwg : Q.map w ≫ g = Q.map f := by
    rw [hg]
    exact (Localization.Construction.wIso (W := W) w hw).hom_inv_id_assoc (Q.map f)
  let N := neighborhoodModelToAmbient S U x
  let w' := N.map w ≫ (i Y).hom
  let f' := N.map f ≫ (i Z).hom
  refine ⟨M.neighborhood.V, M.neighborhood.le_V, M.neighborhood.mem_V,
    N.obj M, M.hom, w', f', ?_, ?_⟩
  · show IsPullback w.left M.hom Y.hom M.neighborhood.V.ι
    apply hw.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso
    · simp
    · simp
    · simp [MY, neighborhoodModelOfFiniteEtale]
    · exact S.homOfLE_ι w.base_le
  · have heq := congrArg (fun k =>
      (GlueingNearPoint.openComponent S U x).map (e.functor.map k)) hwg
    simp only [Functor.map_comp, hmap] at heq
    change (GlueingNearPoint.openComponent S U x).map (e.functor.map (Q.map w)) ≫
      (aY.hom ≫ fUo ≫ aZ.inv) =
      (GlueingNearPoint.openComponent S U x).map (e.functor.map (Q.map f)) at heq
    have key : ∀ (D : FiniteEtaleOver S) (k : M ⟶ neighborhoodModelOfFiniteEtale U x D),
        (GlueingNearPoint.openComponent S U x).map (e.functor.map (Q.map k)) ≫ (aa D).hom =
          (a.app M).hom ≫ (Over.pullback U.ι).map (N.map k ≫ (i D).hom) := by
      intro D k
      have h := congrArg (fun m => m ≫ (Over.pullback U.ι).map (i D).hom) (a.hom.naturality k)
      simpa only [aa, Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc, Functor.comp_map, Iso.app_hom, Q, W, N] using h
    exact conjugate_eq_of_commutative_squares (a.app M) aY aZ _ _
      ((Over.pullback U.ι).map w') ((Over.pullback U.ι).map f') fUo (key Y w) (key Z f) heq

/-! ### Choosing the point at which to extend -/

/-- A proper open subscheme misses a point (the generic point of an irreducible component of its
complement) at which the preimage of the open in the local scheme is exactly the punctured
spectrum. -/
lemma exists_point_with_punctured_local_open
    (S : Scheme.{u}) (U : S.Opens) (hU : U ≠ ⊤) :
    ∃ x : S, x ∉ U ∧ (S.fromSpecStalk x) ⁻¹ᵁ U = puncturedSpectrum (S.presheaf.stalk x) := by
  classical
  obtain ⟨z, hz⟩ : ((U : Set S)ᶜ).Nonempty := by
    by_contra hn
    exact hU (top_unique fun x _ => not_not.mp fun hx => hn ⟨x, hx⟩)
  let Z := (U : Set S)ᶜ
  let z' : Z := ⟨z, hz⟩
  let C := irreducibleComponent z'
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  let : QuasiSober Z := (U.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal).quasiSober
  let x' := hC.genericPoint
  have hg : IsGenericPoint x' C := hC.isGenericPoint_genericPoint isClosed_irreducibleComponent
  refine ⟨x'.val, x'.property, ?_⟩
  ext y
  constructor
  · intro hy heq
    subst y
    change S.fromSpecStalk x'.val (IsLocalRing.closedPoint _) ∈ U at hy
    rw [Scheme.fromSpecStalk_closedPoint] at hy
    exact x'.property hy
  · intro hy
    by_contra hnot
    let y' : Z := ⟨S.fromSpecStalk x'.val y, hnot⟩
    have hspec : S.fromSpecStalk x'.val y ⤳ x'.val := by
      have hm : S.fromSpecStalk x'.val y ∈ Set.range (S.fromSpecStalk x'.val) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hm
    have hmem : x' ∈ closure ({y'} : Set Z) := by
      rw [Topology.IsEmbedding.closure_eq_preimage_closure_image
        (f := (Subtype.val : Z → S)) Topology.IsEmbedding.subtypeVal]
      simpa only [Set.image_singleton, Set.mem_preimage] using hspec.mem_closure
    have hsub : C ⊆ closure ({y'} : Set Z) := by
      rw [← hg.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    have heq : closure ({y'} : Set Z) = C :=
      eq_irreducibleComponent isPreirreducible_singleton.closure hsub
    have hygen : IsGenericPoint y' C := by rw [← heq]; exact isGenericPoint_closure
    have hxy : y'.val = x'.val := congrArg Subtype.val (hygen.eq hg)
    apply hy
    apply (S.fromSpecStalk x'.val).isEmbedding.injective
    simpa only [Scheme.fromSpecStalk_closedPoint] using hxy

/-! ### The inductive step -/

/-- A morphism of covers over `U` extends over the local scheme at `x` compatibly with the
canonical comparison on the overlap, as soon as base change to the punctured local scheme at
`x` is full and faithful. -/
lemma compatible_local_extension
    (S : Scheme.{u}) (U : S.Opens) (x : S)
    (hff : Nonempty (finiteEtaleBaseChange (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).FullyFaithful)
    (Y Z : FiniteEtaleOver S)
    (fU : (finiteEtaleBaseChange U.ι).obj Y ⟶ (finiteEtaleBaseChange U.ι).obj Z) :
    ∃ fA : (finiteEtaleBaseChange (S.fromSpecStalk x)).obj Y ⟶
      (finiteEtaleBaseChange (S.fromSpecStalk x)).obj Z,
      (Over.pullback ((S.fromSpecStalk x) ∣_ U)).map
          (overHomOfFiniteEtaleBaseChange U.ι fU) ≫
        (canonicalOverlapIso S U x (Over.mk Z.hom)).hom =
      (canonicalOverlapIso S U x (Over.mk Y.hom)).hom ≫
        (Over.pullback (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).map
          (overHomOfFiniteEtaleBaseChange (S.fromSpecStalk x) fA) := by
  obtain ⟨ff⟩ := hff
  let F := finiteEtaleBaseChange (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)
  let cY := canonicalOverlapIso S U x (Over.mk Y.hom)
  let cZ := canonicalOverlapIso S U x (Over.mk Z.hom)
  let m := cY.inv ≫ (Over.pullback ((S.fromSpecStalk x) ∣_ U)).map
    (overHomOfFiniteEtaleBaseChange U.ι fU) ≫ cZ.hom
  let m' : F.obj ((finiteEtaleBaseChange (S.fromSpecStalk x)).obj Y) ⟶
      F.obj ((finiteEtaleBaseChange (S.fromSpecStalk x)).obj Z) :=
    MorphismProperty.Over.homMk m.left m.w
  refine ⟨ff.preimage m', ?_⟩
  have hm : (Over.pullback (((S.fromSpecStalk x) ⁻¹ᵁ U).ι)).map
      (overHomOfFiniteEtaleBaseChange (S.fromSpecStalk x) (ff.preimage m')) = m :=
    Over.OverMorphism.ext (congrArg (fun q => q.left) (ff.map_preimage m'))
  rw [hm]
  simp [m, cY, cZ]

/-- A model over `V` cartesian over the first cover is the base change of that cover, so the
map it carries to the second cover is a map out of `Y ×_S V` extending the given morphism of
covers over `U`. -/
lemma extension_of_cartesian_model
    {S : Scheme.{u}} {U V : S.Opens} (hUV : U ≤ V)
    (Y Z : FiniteEtaleOver S)
    (fU : (finiteEtaleBaseChange U.ι).obj Y ⟶ (finiteEtaleBaseChange U.ι).obj Z)
    (T : Over S) (p : T.left ⟶ V.toScheme)
    (w : T ⟶ Over.mk Y.hom) (f : T ⟶ Over.mk Z.hom)
    (hw : IsPullback w.left p Y.hom V.ι)
    (heq : (Over.pullback U.ι).map w ≫ overHomOfFiniteEtaleBaseChange U.ι fU =
      (Over.pullback U.ι).map f) :
    ∃ t : pullback Y.hom V.ι ⟶ Z.left,
      t ≫ Z.hom = pullback.snd Y.hom V.ι ≫ V.ι ∧
      openPullbackMap Y.hom hUV ≫ t = fU.left ≫ pullback.fst Z.hom U.ι := by
  let e := hw.isoPullback
  let t := e.inv ≫ f.left
  have ht : t ≫ Z.hom = pullback.snd Y.hom V.ι ≫ V.ι := by
    have hfw : f.left ≫ Z.hom = T.hom := f.w
    have hww : w.left ≫ Y.hom = T.hom := w.w
    rw [Category.assoc, hfw, ← hww, ← Category.assoc]
    show (hw.isoPullback.inv ≫ w.left) ≫ Y.hom = _
    rw [hw.isoPullback_inv_fst, pullback.condition]
  refine ⟨t, ht, ?_⟩
  let l := openPullbackMap Y.hom hUV ≫ e.inv
  have hlw : l ≫ w.left = pullback.fst Y.hom U.ι := by
    dsimp [l, e]
    rw [Category.assoc, hw.isoPullback_inv_fst, openPullbackMap_fst]
  have hl : l ≫ T.hom = pullback.snd Y.hom U.ι ≫ U.ι := by
    rw [← w.w, ← Category.assoc, hlw]
    exact pullback.condition
  let wU : pullback T.hom U.ι ⟶ pullback Y.hom U.ι := ((Over.pullback U.ι).map w).left
  let fUl : pullback Y.hom U.ι ⟶ pullback Z.hom U.ι := fU.left
  let fUT : pullback T.hom U.ι ⟶ pullback Z.hom U.ι := ((Over.pullback U.ι).map f).left
  have hwfst : wU ≫ pullback.fst Y.hom U.ι = pullback.fst T.hom U.ι ≫ w.left :=
    pullback.lift_fst _ _ _
  have hwsnd : wU ≫ pullback.snd Y.hom U.ι = pullback.snd T.hom U.ι :=
    pullback.lift_snd _ _ _
  obtain ⟨j, hjfst, hjsnd⟩ := pullback.lift' l (pullback.snd Y.hom U.ι) hl
  have hjw : j ≫ wU = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hwfst, ← Category.assoc, hjfst, hlw, Category.id_comp]
    · rw [Category.assoc, hwsnd, hjsnd, Category.id_comp]
  have hleft : wU ≫ fUl = fUT := congrArg (fun q => q.left) heq
  have hfst : fUT ≫ pullback.fst Z.hom U.ι = pullback.fst T.hom U.ι ≫ f.left :=
    pullback.lift_fst _ _ _
  show l ≫ f.left = fUl ≫ pullback.fst Z.hom U.ι
  calc
    l ≫ f.left = (j ≫ pullback.fst T.hom U.ι) ≫ f.left := by rw [hjfst]
    _ = j ≫ (fUT ≫ pullback.fst Z.hom U.ι) := by rw [hfst, Category.assoc]
    _ = (j ≫ wU) ≫ fUl ≫ pullback.fst Z.hom U.ι := by
      rw [← hleft]
      simp only [Category.assoc]
    _ = fUl ≫ pullback.fst Z.hom U.ι := by rw [hjw, Category.id_comp]

/-- Let `V` be a retrocompact open of a scheme `X` and let `x` be a point outside `V` whose local
scheme meets `V` exactly in the punctured spectrum of `𝒪_{X, x}`, and suppose the punctured
spectrum of every strict henselization of `𝒪_{X, x}` is connected.  Then a morphism between the
base changes to `V` of two finite étale covers `Y` and `Z` of `X` extends to a morphism over an
open `W` containing both `V` and `x`.

The morphism over `V` is carried by its underlying map `Y ×_X V ⟶ Z`, and the extension
restricts to it along `AlgebraicGeometry.openPullbackMap`. -/
theorem exists_opens_extension_of_connected_puncturedSpectrum
    {X : Scheme.{u}} (V : X.Opens) (hV : IsRetrocompact (V : Set X)) (x : X) (hx : x ∉ V)
    (hpunct : (X.fromSpecStalk x) ⁻¹ᵁ V = puncturedSpectrum (X.presheaf.stalk x))
    (hconn : IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    (Y Z : FiniteEtaleOver X)
    (fV : (finiteEtaleBaseChange V.ι).obj Y ⟶ (finiteEtaleBaseChange V.ι).obj Z) :
    ∃ (W : X.Opens) (hVW : V ≤ W), x ∈ W ∧
      ∃ t : pullback Y.hom W.ι ⟶ Z.left,
        t ≫ Z.hom = pullback.snd Y.hom W.ι ≫ W.ι ∧
        openPullbackMap Y.hom hVW ≫ t = fV.left ≫ pullback.fst Z.hom V.ι := by
  have hff : Nonempty (finiteEtaleBaseChange (((X.fromSpecStalk x) ⁻¹ᵁ V).ι)).FullyFaithful := by
    rw [hpunct]
    exact nonempty_fullyFaithful_puncturedSpectrum_of_connected (X.presheaf.stalk x) hconn
  obtain ⟨fA, hc⟩ := compatible_local_extension X V x hff Y Z fV
  obtain ⟨W, hVW, hxW, T, p, w, f, hw, heq⟩ :=
    spread_finiteEtale_hom_from_gluingData X V x hx hV Y Z fV fA hc
  exact ⟨W, hVW, hxW, extension_of_cartesian_model hVW Y Z fV T p w f hw heq⟩

/-! ### The theorem -/

/-- Let `U` be a dense open of a scheme `X` with Noetherian underlying space, and suppose that for
every point `x` of `X` outside `U` the punctured spectrum of every strict henselization of
`𝒪_{X, x}` is connected.  Then base change of finite étale covers along `U ⟶ X` is fully
faithful. -/
@[stacks 0BQF, sga "7 II 2.3.1" "partial"]
theorem fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace
    (X : Scheme.{u}) (U : X.Opens) [NoetherianSpace X] (hU : Dense (U : Set X))
    (hconn : ∀ x : X, x ∉ U →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  classical
  let F := finiteEtaleBaseChange U.ι
  let : IsDominant U.ι := Opens.isDominant_ι hU
  let : F.Faithful := faithful_finiteEtaleBaseChange_of_isDominant U.ι
  have hfull : F.Full := by
    constructor
    intro Y Z fU
    let fUl : pullback Y.hom U.ι ⟶ pullback Z.hom U.ι := fU.left
    have hfUl : fUl ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
      MorphismProperty.Over.w fU
    let P (V : X.Opens) : Prop := ∃ hUV : U ≤ V,
      ∃ t : pullback Y.hom V.ι ⟶ Z.left,
        t ≫ Z.hom = pullback.snd Y.hom V.ι ≫ V.ι ∧
        openPullbackMap Y.hom hUV ≫ t = fUl ≫ pullback.fst Z.hom U.ι
    have htop : P ⊤ := by
      apply WellFoundedGT.induction_top
      · refine ⟨U, le_rfl, fUl ≫ pullback.fst Z.hom U.ι, ?_, ?_⟩
        · rw [Category.assoc, pullback.condition, ← Category.assoc, hfUl]
        · rw [openPullbackMap_refl, Category.id_comp]
      · intro V hV hPV
        obtain ⟨hUV, t, ht, hext⟩ := hPV
        obtain ⟨x, hx, hpunct⟩ := exists_point_with_punctured_local_open X V hV
        obtain ⟨tv, htvfst, htvsnd⟩ := pullback.lift' t (pullback.snd Y.hom V.ι) ht
        let fV : (finiteEtaleBaseChange V.ι).obj Y ⟶ (finiteEtaleBaseChange V.ι).obj Z :=
          MorphismProperty.Over.homMk tv htvsnd
        obtain ⟨W, hVW, hxW, tW, htW, hextW⟩ :=
          exists_opens_extension_of_connected_puncturedSpectrum V
            (noetherianSpace_isRetrocompact X _) x hx hpunct
            (hconn x (fun hxU => hx (hUV hxU))) Y Z fV
        refine ⟨W, lt_of_le_of_ne hVW (fun h => hx (h ▸ hxW)), hUV.trans hVW, tW, htW, ?_⟩
        rw [← openPullbackMap_comp Y.hom hUV hVW, Category.assoc, hextW]
        show openPullbackMap Y.hom hUV ≫ tv ≫ pullback.fst Z.hom V.ι =
          fUl ≫ pullback.fst Z.hom U.ι
        rwa [htvfst]
    obtain ⟨hUt, t, ht, hext⟩ := htop
    have hιiso : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
    have hπ : IsIso (pullback.fst Y.hom (⊤ : X.Opens).ι) :=
      (IsPullback.of_hasPullback Y.hom (⊤ : X.Opens).ι).isIso_fst_of_isIso
    have hgw : (inv (pullback.fst Y.hom (⊤ : X.Opens).ι) ≫ t) ≫ Z.hom = Y.hom := by
      rw [Category.assoc, ht, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
        Category.id_comp]
    let g : Y ⟶ Z :=
      MorphismProperty.Over.homMk (inv (pullback.fst Y.hom (⊤ : X.Opens).ι) ≫ t) hgw
    have hgfst : (F.map g).left ≫ pullback.fst Z.hom U.ι =
        pullback.fst Y.hom U.ι ≫ g.left := finiteEtaleBaseChange_map_left_fst U.ι g
    have hgsnd : (F.map g).left ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
      MorphismProperty.Over.w (F.map g)
    have hinvfst : pullback.fst Y.hom U.ι ≫ inv (pullback.fst Y.hom (⊤ : X.Opens).ι) =
        openPullbackMap Y.hom hUt := by
      apply (cancel_mono (pullback.fst Y.hom (⊤ : X.Opens).ι)).mp
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, openPullbackMap_fst]
    refine ⟨g, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · show (F.map g).left ≫ pullback.fst Z.hom U.ι = fUl ≫ pullback.fst Z.hom U.ι
      rw [hgfst]
      show pullback.fst Y.hom U.ι ≫ inv (pullback.fst Y.hom (⊤ : X.Opens).ι) ≫ t =
        fUl ≫ pullback.fst Z.hom U.ι
      rwa [← Category.assoc, hinvfst]
    · show (F.map g).left ≫ pullback.snd Z.hom U.ι = fUl ≫ pullback.snd Z.hom U.ι
      rw [hgsnd, hfUl]
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

end AlgebraicGeometry

end

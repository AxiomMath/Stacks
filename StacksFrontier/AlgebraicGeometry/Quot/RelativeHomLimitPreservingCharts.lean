module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The relative Hom functor as an equalizer over two charts

In the standing data of Stacks 08JT let `a : U ⟶ X` be surjective and étale and let
`b : V ⟶ U ×_X U` be surjective and étale.  Stacks 08K3 presents `Hom(F, G)(T)` as the equalizer
of the two restrictions

`Hom(F|_U, G|_U)(T) ⇉ Hom(F|_V, G|_V)(T)`,

and this is the step of the proof of Stacks 08K4 which "reduces us to the case that `X` is
affine": limit preservation passes to an equalizer
(`AlgebraicGeometry.limitPreserving_of_isEqualizer`), so `Hom(F, G)` is limit preserving as soon
as the relative Hom functors of the two charts are.

The three presheaves and the two parallel arrows are
built by whiskering `AlgebraicGeometry.Space.moduleHomOver`, the relative Hom functor indexed by
the algebraic spaces over `X`, with functors to `Over X`, so that their naturality in the test
scheme is that of `moduleHomOver` and needs no further coherence.  The presheaf of a chart is then
identified with the relative Hom functor of the chart, regarded as a situation of Stacks 08JT on
its own (`AlgebraicGeometry.Space.HomSituation.restrictSituation`), through Stacks 08JW's
`AlgebraicGeometry.Space.moduleHomOverPullback` and the pasting of cartesian squares.

## Main definitions

* `AlgebraicGeometry.Space.overBaseChangeCounit`: the projections `Z ×_X W ⟶ W`, as a natural
  transformation of functors on the algebraic spaces over `X`.
* `AlgebraicGeometry.Space.overBaseChangeLift`: the morphisms `D ×_X W ⟶ Z ×_X W` induced by a
  morphism `D ⟶ Z` over `X`.
* `AlgebraicGeometry.Space.overBaseChangeCompIso`: the pasting `Z ×_Y W ≅ Z ×_X (X ×_Y W)`.
* `AlgebraicGeometry.Space.HomSituation.restrictSituation`: the situation of Stacks 08JT
  obtained by restricting the two modules along a morphism `c : Z ⟶ X`.
* `AlgebraicGeometry.Space.HomSituation.chartHomFunctor`: `T ↦ Hom(F|_Z, G|_Z)(T)` as a presheaf
  built from `moduleHomOver`, and `AlgebraicGeometry.Space.HomSituation.chartRestriction` and
  `AlgebraicGeometry.Space.HomSituation.chartLift` the restrictions between such presheaves.

## Main results

* `AlgebraicGeometry.Space.HomSituation.chartHomFunctorIso`: the presheaf of a chart is the
  relative Hom functor of the restricted situation.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_charts`: **the chart step
  of the proof of Stacks 08K4.**  If `a : U ⟶ X` and `b : V ⟶ U ×_X U` are surjective and étale
  and the relative Hom functors of the restrictions of the situation to `U` and to `V` are limit
  preserving, then so is `Hom(F, G)`.

## References

* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
* [Stacks Project, Tag 08K3](https://stacks.math.columbia.edu/tag/08K3)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The base change of a chart along the test schemes -/

namespace HomSituation

variable (s : HomSituation B S hS)

section Chart

variable {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X)

/-- The morphism `Z ×_X X_{T'} ⟶ Z ×_X X_T` induced by a morphism `T' ⟶ T` of test schemes. -/
def chartMap {T' T : s.SchemesOver} (g : T' ⟶ T) :
    AlgebraicSpaces.fiberProduct B S hS c (s.projection T') ⟶
      AlgebraicSpaces.fiberProduct B S hS c (s.projection T) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift
    (fiberFst c (s.projection T')) (fiberSnd c (s.projection T') ≫ baseChangeMap s.f g) (by
      rw [Category.assoc, baseChangeMap_comp_projection]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T')).w)

/-- `chartMap` commutes with the projections to `Z`. -/
@[reassoc (attr := simp)]
theorem chartMap_fst {T' T : s.SchemesOver} (g : T' ⟶ T) :
    s.chartMap c g ≫ fiberFst c (s.projection T) = fiberFst c (s.projection T') :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift_fst _ _ _

/-- `chartMap` lies over the base change map `X_{T'} ⟶ X_T`. -/
@[reassoc (attr := simp)]
theorem chartMap_snd {T' T : s.SchemesOver} (g : T' ⟶ T) :
    s.chartMap c g ≫ fiberSnd c (s.projection T) =
      fiberSnd c (s.projection T') ≫ baseChangeMap s.f g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift_snd _ _ _

/-- A morphism into `Z ×_X X_T` is determined by its two projections. -/
theorem chart_hom_ext {T : s.SchemesOver} {W : AlgebraicSpaces B S hS}
    {k l : W ⟶ AlgebraicSpaces.fiberProduct B S hS c (s.projection T)}
    (h₁ : k ≫ fiberFst c (s.projection T) = l ≫ fiberFst c (s.projection T))
    (h₂ : k ≫ fiberSnd c (s.projection T) = l ≫ fiberSnd c (s.projection T)) : k = l :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).hom_ext h₁ h₂

/-- **The base change of a chart `c : Z ⟶ X` along the test schemes**, read over `X`: a test
scheme `T` is sent to `Z ×_X X_T` with its structure morphism through `Z`.  For a member of a
covering of `X` this is `AlgebraicGeometry.Space.HomSituation.memberSpace` with
`AlgebraicGeometry.Space.HomSituation.memberToSource`, and for a member of a covering of an
overlap it is `AlgebraicGeometry.Space.HomSituation.tripleSpace` with
`AlgebraicGeometry.Space.HomSituation.tripleToX`. -/
def chartOver : s.SchemesOver ⥤ Over s.X where
  obj T := Over.mk (fiberFst c (s.projection T) ≫ c)
  map g := Over.homMk (s.chartMap c g) (by
    change s.chartMap c g ≫ fiberFst c _ ≫ c = fiberFst c _ ≫ c
    rw [chartMap_fst_assoc])
  map_id T := by
    refine Over.OverMorphism.ext (s.chart_hom_ext c ?_ ?_) <;>
      change s.chartMap c (𝟙 T) ≫ _ = 𝟙 _ ≫ _ <;> simp
  map_comp g h := by
    refine Over.OverMorphism.ext (s.chart_hom_ext c ?_ ?_) <;>
      change s.chartMap c (g ≫ h) ≫ _ = (s.chartMap c g ≫ s.chartMap c h) ≫ _ <;>
      simp [baseChangeMap_comp]

/-- The projections `Z ×_X X_T ⟶ X_T`, as a natural transformation over `X`. -/
def chartToBase : s.chartOver c ⟶ baseChangeOver s.f where
  app T := Over.homMk (fiberSnd c (s.projection T))
    (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).w.symm
  naturality _ _ g := Over.OverMorphism.ext (s.chartMap_snd c g)

variable {D : AlgebraicSpaces B S hS} (m : D ⟶ Z) (d : D ⟶ s.X) (h : m ≫ c = d)

/-- The morphism `D ×_X X_T ⟶ Z ×_X X_T` induced by `m : D ⟶ Z` with `m ≫ c = d`. -/
def chartLiftHom (T : s.SchemesOver) :
    AlgebraicSpaces.fiberProduct B S hS d (s.projection T) ⟶
      AlgebraicSpaces.fiberProduct B S hS c (s.projection T) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift
    (fiberFst d (s.projection T) ≫ m) (fiberSnd d (s.projection T)) (by
      rw [Category.assoc, h]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS d (s.projection T)).w)

/-- `chartLiftHom` lies over `m : D ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem chartLiftHom_fst (T : s.SchemesOver) :
    s.chartLiftHom c m d h T ≫ fiberFst c (s.projection T) = fiberFst d (s.projection T) ≫ m :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift_fst _ _ _

/-- `chartLiftHom` commutes with the projections to `X_T`. -/
@[reassoc (attr := simp)]
theorem chartLiftHom_snd (T : s.SchemesOver) :
    s.chartLiftHom c m d h T ≫ fiberSnd c (s.projection T) = fiberSnd d (s.projection T) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T)).lift_snd _ _ _

/-- The morphisms `D ×_X X_T ⟶ Z ×_X X_T` induced by `m : D ⟶ Z` over `X`, as a natural
transformation over `X`. -/
def chartLiftNat : s.chartOver d ⟶ s.chartOver c where
  app T := Over.homMk (s.chartLiftHom c m d h T) (by
    change s.chartLiftHom c m d h T ≫ fiberFst c _ ≫ c = fiberFst d _ ≫ d
    rw [chartLiftHom_fst_assoc, h])
  naturality T' T g := by
    refine Over.OverMorphism.ext (s.chart_hom_ext c ?_ ?_) <;>
      change (s.chartMap d g ≫ s.chartLiftHom c m d h T) ≫ _ =
        (s.chartLiftHom c m d h T' ≫ s.chartMap c g) ≫ _ <;> simp

end Chart

/-! ### The presheaves of the charts -/

/-- **The restriction of the standing data of Stacks 08JT along a morphism `c : Z ⟶ X`**: the
algebraic space `Z` over the base through `c ≫ f`, with the two modules pulled back along `c`.
They are quasi-coherent by Stacks 03GA. -/
abbrev restrictSituation {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) : HomSituation B S hS where
  X := Z
  base := s.base
  f := c ≫ s.f
  F := (modulePullback B S hS c).obj s.F
  G := (modulePullback B S hS c).obj s.G
  quasicoherent_F :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c s.F s.quasicoherent_F
  quasicoherent_G :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c s.G s.quasicoherent_G

/-- **The relative Hom functor of a chart `c : Z ⟶ X`, built from `moduleHomOver`**: its value at
a test scheme `T` is the set of homomorphisms of the pullbacks of `F` and `G` to `Z ×_X X_T`. -/
abbrev chartHomFunctor {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) :
    (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1) :=
  (s.chartOver c).op ⋙ moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G

/-- Restriction from `X_T` to `Z ×_X X_T`. -/
abbrev chartRestriction {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) :
    s.homFunctor (modulePushforwardCoherence B S hS) ⟶ s.chartHomFunctor c :=
  Functor.whiskerRight (NatTrans.op (s.chartToBase c))
    (moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G)

/-- Restriction from `Z ×_X X_T` to `D ×_X X_T` along a morphism `m : D ⟶ Z` over `X`. -/
abbrev chartLift {D Z : AlgebraicSpaces B S hS} (m : D ⟶ Z) (c : Z ⟶ s.X) (d : D ⟶ s.X)
    (h : m ≫ c = d) : s.chartHomFunctor c ⟶ s.chartHomFunctor d :=
  Functor.whiskerRight (NatTrans.op (s.chartLiftNat c m d h))
    (moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G)

/-- The restriction to a chart is the restriction of homomorphisms of inverse images along the
projection `Z ×_X X_T ⟶ X_T`. -/
theorem chartRestriction_app {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) (T : (s.SchemesOver)ᵒᵖ)
    (β : s.homAt T.unop) :
    (s.chartRestriction c).app T β =
      restrictPullbackHom (fiberSnd c (s.projection T.unop))
        (AlgebraicSpaces.isPullback_fiberProduct B S hS c (s.projection T.unop)).w.symm
        (s.toModuleHom β) := by
  rw [Functor.whiskerRight_app, moduleHomOver_map]
  exact TypeCat.ofHom_apply _ _

/-- The restriction between two charts is the restriction of homomorphisms of inverse images
along the induced morphism of base changes. -/
theorem chartLift_app {D Z : AlgebraicSpaces B S hS} (m : D ⟶ Z) (c : Z ⟶ s.X) (d : D ⟶ s.X)
    (h : m ≫ c = d) (T : (s.SchemesOver)ᵒᵖ)
    (α : (modulePullback B S hS (fiberFst c (s.projection T.unop) ≫ c)).obj s.F ⟶
      (modulePullback B S hS (fiberFst c (s.projection T.unop) ≫ c)).obj s.G) :
    (s.chartLift m c d h).app T α =
      restrictPullbackHom (s.chartLiftHom c m d h T.unop)
        (Over.w ((s.chartLiftNat c m d h).app T.unop)) α := by
  rw [Functor.whiskerRight_app, moduleHomOver_map]
  exact TypeCat.ofHom_apply _ _

/-- The pasting identification `Z ×_X X_T ≅ Z ×_{base} T` for `c : Z ⟶ X`. -/
def chartBaseChangeIso {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) (T : s.SchemesOver) :
    AlgebraicSpaces.fiberProduct B S hS c (s.projection T) ≅ baseChangeSpace (c ≫ s.f) T :=
  ObjectProperty.isoMk _ (pullbackRightPullbackFstIso s.f.hom T.hom.hom c.hom)

/-- `chartBaseChangeIso` commutes with the projections to `Z`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeIso_hom_projection {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X)
    (T : s.SchemesOver) :
    (s.chartBaseChangeIso c T).hom ≫ baseChangeProjection (c ≫ s.f) T =
      fiberFst c (s.projection T) :=
  ObjectProperty.hom_ext _ (pullbackRightPullbackFstIso_hom_fst _ _ _)

/-- `chartBaseChangeIso` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeIso_hom_inclusion {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X)
    (T : s.SchemesOver) :
    (s.chartBaseChangeIso c T).hom ≫ baseChangeInclusion (c ≫ s.f) T =
      fiberSnd c (s.projection T) ≫ baseChangeInclusion s.f T :=
  ObjectProperty.hom_ext _ (pullbackRightPullbackFstIso_hom_snd _ _ _)

/-- The pasting identification is natural in the test scheme. -/
theorem chartBaseChangeIso_naturality {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X)
    {T' T : s.SchemesOver} (g : T' ⟶ T) :
    s.chartMap c g ≫ (s.chartBaseChangeIso c T).hom =
      (s.chartBaseChangeIso c T').hom ≫ baseChangeMap (c ≫ s.f) g := by
  refine baseChange_hom_ext (c ≫ s.f) ?_ ?_ <;> simp

/-- The base change of a chart along the test schemes, read over `X`, is the base change of the
restricted situation followed by composition with `c`. -/
def chartOverIso {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) :
    s.chartOver c ≅ baseChangeOver (c ≫ s.f) ⋙ Over.map c :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (s.chartBaseChangeIso c T) (by
      change (s.chartBaseChangeIso c T).hom ≫ baseChangeProjection (c ≫ s.f) T ≫ c =
        fiberFst c (s.projection T) ≫ c
      rw [chartBaseChangeIso_hom_projection_assoc]))
    (fun g ↦ Over.OverMorphism.ext (s.chartBaseChangeIso_naturality c g))

/-- **The presheaf of a chart is the relative Hom functor of the restricted situation.**  This is
Stacks 08JW's `AlgebraicGeometry.Space.moduleHomOverPullback` along `c`, followed by the pasting
`Z ×_X X_T ≅ Z ×_{base} T`. -/
def chartHomFunctorIso {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X) :
    (s.restrictSituation c).homFunctor (modulePushforwardCoherence B S hS) ≅
      s.chartHomFunctor c :=
  Functor.isoWhiskerLeft (baseChangeOver (c ≫ s.f)).op
      (moduleHomOverPullback (modulePushforwardCoherence B S hS) c s.F s.G) ≪≫
    Functor.isoWhiskerRight (NatIso.op (s.chartOverIso c))
      (moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G)

/-- Limit preservation of the presheaf of a chart, from that of the relative Hom functor of the
restricted situation. -/
theorem limitPreserving_chartHomFunctor {Z : AlgebraicSpaces B S hS} (c : Z ⟶ s.X)
    (h : LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      ((s.restrictSituation c).homFunctor (modulePushforwardCoherence B S hS))) :
    LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor (s.chartHomFunctor c) :=
  limitPreserving_of_natIso (s.chartHomFunctorIso c) h

variable {U V : AlgebraicSpaces B S hS} (a : U ⟶ s.X)
  (b : V ⟶ overlapSpace (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit)

/-- **The chart step of the proof of Stacks 08K4.**  Let `a : U ⟶ X` be surjective and étale and
let `b : V ⟶ U ×_X U` be surjective and étale.  If the relative Hom functors of the restrictions
of the situation to `U` and to `V` are limit preserving, so is `Hom(F, G)`.

By Stacks 08K3, applied to the one-member coverings `{U ⟶ X}` and `{V ⟶ U ×_X U}`, the
restriction `Hom(F, G)(T) ⟶ Hom(F|_U, G|_U)(T)` is injective with image the equalizer of the two
restrictions to `Hom(F|_V, G|_V)(T)`; limit preservation passes to such an equalizer. -/
theorem limitPreserving_homFunctor_of_charts
    (ha : IsEtale B S hS a.hom) (ha' : IsSurjective B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hb' : IsSurjective B S hS b.hom)
    (hU : LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      ((s.restrictSituation a).homFunctor (modulePushforwardCoherence B S hS)))
    (hV : LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      ((s.restrictSituation (b ≫ overlapFst (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit ≫
        a)).homFunctor (modulePushforwardCoherence B S hS))) :
    LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      (s.homFunctor (modulePushforwardCoherence B S hS)) := by
  have hcovU : IsFppfCovering B S hS (fun _ : PUnit.{1} ↦ U.1) fun _ ↦ a.hom :=
    isFppfCovering_singleton.{u, 0} B S hS a ha' (isFlat_of_isEtale B S hS ha)
      (isLocallyOfFinitePresentation_of_isEtale B S hS ha)
  have hcovV : ∀ i j : PUnit.{1}, IsFppfCovering B S hS (fun _ : PUnit.{1} ↦ V.1)
      fun _ ↦ b.hom := fun _ _ ↦
    isFppfCovering_singleton.{u, 0} B S hS b hb' (isFlat_of_isEtale B S hS hb)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hb)
  have key := fun (T : (s.SchemesOver)ᵒᵖ) ↦
    s.tripleRestrictionsAgree_iff_existsUnique_sourceHom (fun _ : PUnit.{1} ↦ a) T.unop
      (K := fun _ _ ↦ PUnit.{1}) (fun _ _ _ ↦ b) hcovU hcovV
  have hagree := fun (T : (s.SchemesOver)ᵒᵖ) (β : s.homAt T.unop) ↦
    s.tripleRestrictionsAgree_restrict (fun _ : PUnit.{1} ↦ a) T.unop
      (K := fun _ _ ↦ PUnit.{1}) (fun _ _ _ ↦ b) β
  have hres : ∀ (T : (s.SchemesOver)ᵒᵖ) (β : s.homAt T.unop),
      (s.chartRestriction a).app T β =
        restrictPullbackHom (s.memberInclusion (fun _ : PUnit.{1} ↦ a) T.unop PUnit.unit)
          (s.memberInclusion_comp (fun _ : PUnit.{1} ↦ a) T.unop PUnit.unit)
          (s.toModuleHom β) :=
    fun T β ↦ s.chartRestriction_app a T β
  have hsnd : (b ≫ overlapSnd (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit) ≫ a =
      s.tripleToSource (fun _ : PUnit.{1} ↦ a) (K := fun _ _ ↦ PUnit.{1})
        (fun _ _ _ ↦ b) PUnit.unit PUnit.unit PUnit.unit :=
    (Category.assoc _ _ _).trans
      (s.tripleToSource_eq (fun _ : PUnit.{1} ↦ a) (K := fun _ _ ↦ PUnit.{1})
        (fun _ _ _ ↦ b) PUnit.unit PUnit.unit PUnit.unit)
  refine limitPreserving_of_isEqualizer s.testSchemeFunctor (s.chartRestriction a)
    (s.chartLift (b ≫ overlapFst (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit) a _ rfl)
    (s.chartLift (b ≫ overlapSnd (fun _ : PUnit.{1} ↦ a) PUnit.unit PUnit.unit) a _ hsnd)
    ?_ ?_ ?_ (s.limitPreserving_chartHomFunctor a hU) (s.limitPreserving_chartHomFunctor _ hV)
  · intro T β β' h
    obtain ⟨γ, -, hγ⟩ := (key T _).mp (hagree T β)
    exact (hγ β fun _ ↦ rfl).trans
      (hγ β' fun _ ↦ ((hres T β').symm.trans (h.symm.trans (hres T β)))).symm
  · intro T β
    rw [hres T β]
    exact (s.chartLift_app _ a _ rfl T _).trans
      (((hagree T β) PUnit.unit PUnit.unit PUnit.unit).trans
        (s.chartLift_app _ a _ hsnd T _).symm)
  · intro T q hq
    obtain ⟨β, hβ, -⟩ := (key T fun _ ↦ q).mp fun _ _ _ ↦
      (s.chartLift_app _ a _ rfl T q).symm.trans
        (hq.trans (s.chartLift_app _ a _ hsnd T q))
    exact ⟨β, (hres T β).trans (hβ PUnit.unit)⟩

end HomSituation

end AlgebraicGeometry.Space

end

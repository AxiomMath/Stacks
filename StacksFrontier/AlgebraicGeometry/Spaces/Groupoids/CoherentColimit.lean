module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentCofree
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentRightAdjointUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubobjectDirectedSupremum
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentColimits

/-!
# Coherent approximation of a quasi-coherent module on a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` with `U` and `R` Noetherian and
with `s` and `t` flat, quasi-compact and quasi-separated.  Stacks 0GPS asserts that every
quasi-coherent module `(ℱ, β)` on it is a filtered colimit of coherent modules.

The approximating modules are the ones of the source: for a coherent submodule `ℋ` of `ℱ`, the
submodule `ℱ ∩ s_*t^*ℋ` of `ℱ` cut out, in the sense of Stacks 0GPR, by
`t^*ℋ ⟶ t^*ℱ ⟶ s^*ℱ`.  It is coherent by Stacks 0GPR, and it is the underlying module of the fibre
product on the groupoid of the unit `(ℱ, β) ⟶ (s_*t^*ℱ, α)` with `(s_*t^*ℋ, α) ⟶ (s_*t^*ℱ, α)`,
which is how it acquires a transition morphism.

## Main results

* `AlgebraicGeometry.Space.exists_le_of_le_iSup_of_isCoherent` (in
  `StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubobjectDirectedSupremum`) and
  `AlgebraicGeometry.Space.QuasicoherentModule.exists_le_intersectionPushforward`: every coherent
  submodule `ℋ` of `ℱ` lies in `ℱ ∩ s_*t^*ℋ'` for some coherent submodule `ℋ'`.
* `AlgebraicGeometry.Space.QuasicoherentModule.isColimitOfUnderlying` and
  `AlgebraicGeometry.Space.QuasicoherentModule.isColimit_of_iSup_eq_top`: a filtered diagram of
  submodules of a quasi-coherent module on the groupoid whose underlying submodules exhaust it has
  that module as its colimit.
* `AlgebraicGeometry.Space.QuasicoherentModule.exists_isPullback_of_isFlat`: for `s` flat, fibre
  products of quasi-coherent modules on the groupoid exist and are computed on the underlying
  modules.
* `QuasicoherentModule.isCoherent_intersectionPushforward_transitionInclusion`:
  `ℱ ∩ s_*t^*ℋ` is coherent.
* `AlgebraicGeometry.Space.QuasicoherentModule.exists_filtered_diagram_isCoherent`:
  **Stacks 0GPS**.

## Implementation notes

The source deduces that the `ℱ ∩ s_*t^*ℋ` exhaust `ℱ` from the fact that `s_*` commutes with
filtered colimits.  The argument here avoids that: every coherent submodule `ℋ` of `ℱ` lies in
some `ℱ ∩ s_*t^*ℋ'`, because the image of `s^*ℋ` under `β⁻¹` is a coherent submodule of `t^*ℱ` on
the Noetherian space `R`, and `t^*ℱ` is the directed union of the `t^*ℋ'`; a coherent submodule of
a directed union of quasi-coherent submodules lies in one of them by the ascending chain condition
of Stacks 07UJ.  Since the coherent submodules exhaust `ℱ` by Stacks 07UV, so do the
`ℱ ∩ s_*t^*ℋ`.

## References

* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
* [Stacks Project, Tag 0GPR](https://stacks.math.columbia.edu/tag/0GPR)
* [Stacks Project, Tag 0GPP](https://stacks.math.columbia.edu/tag/0GPP)
* [Stacks Project, Tag 0GPQ](https://stacks.math.columbia.edu/tag/0GPQ)
* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 07UJ](https://stacks.math.columbia.edu/tag/07UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-! ### Lifting into `F ∩ f_*G` -/

section Intersection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **A morphism into `F` whose inverse image factors through `φ` factors through `F ∩ f_*G`.**
For `k : H ⟶ F` and `l : f^*H ⟶ G` with `l ≫ φ = f^*k`, the composite of `k` with the unit
`F ⟶ f_*f^*F` is the composite of the unit `H ⟶ f_*f^*H`, of `f_*l` and of `f_*φ`, by
naturality of the unit; so `k` and `H ⟶ f_*f^*H ⟶ f_*G` define a morphism into the fibre
product. -/
def intersectionPushforwardLift (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    {H : Modules.{u, u} B S hS X.1 X.2} (k : H ⟶ F)
    (l : (modulePullback B S hS f).obj H ⟶ G) (hl : l ≫ φ = (modulePullback B S hS f).map k) :
    H ⟶ intersectionPushforward B S hS f φ :=
  pullback.lift k (pullbackPushforwardUnit B S hS f H ≫ (modulePushforward B S hS f).map l) (by
    rw [Category.assoc, ← Functor.map_comp, hl]
    exact (modulePullbackAdjunction B S hS f).unit.naturality k)

/-- The lift `intersectionPushforwardLift` composed with the inclusion of `F ∩ f_*G` into `F`
is `k`. -/
@[reassoc (attr := simp)]
theorem intersectionPushforwardLift_ι (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    {H : Modules.{u, u} B S hS X.1 X.2} (k : H ⟶ F)
    (l : (modulePullback B S hS f).obj H ⟶ G) (hl : l ≫ φ = (modulePullback B S hS f).map k) :
    intersectionPushforwardLift B S hS f φ k l hl ≫ intersectionPushforwardι B S hS f φ = k :=
  pullback.lift_fst _ _ _

/-- **`F ∩ f_*G` is functorial in `G` over `f^*F`.**  A morphism `g : G ⟶ G'` with
`g ≫ φ' = φ` induces `F ∩ f_*G ⟶ F ∩ f_*G'` over `F`. -/
def intersectionPushforwardMap (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G G' : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    (φ' : G' ⟶ (modulePullback B S hS f).obj F) (g : G ⟶ G') (hg : g ≫ φ' = φ) :
    intersectionPushforward B S hS f φ ⟶ intersectionPushforward B S hS f φ' :=
  pullback.lift (intersectionPushforwardι B S hS f φ)
    (intersectionPushforwardπ B S hS f φ ≫ (modulePushforward B S hS f).map g) (by
      rw [Category.assoc, ← Functor.map_comp, hg]
      exact pullback.condition)

/-- The morphism `intersectionPushforwardMap` lies over `F`: composed with the inclusion of
`F ∩ f_*G'` into `F`, it is the inclusion of `F ∩ f_*G` into `F`. -/
@[reassoc (attr := simp)]
theorem intersectionPushforwardMap_ι (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G G' : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    (φ' : G' ⟶ (modulePullback B S hS f).obj F) (g : G ⟶ G') (hg : g ≫ φ' = φ) :
    intersectionPushforwardMap B S hS f φ φ' g hg ≫ intersectionPushforwardι B S hS f φ' =
      intersectionPushforwardι B S hS f φ :=
  pullback.lift_fst _ _ _

end Intersection

namespace QuasicoherentModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-! ### Colimits detected on the underlying modules -/

/-- The naturality of a cocone with constant vertex, read on the underlying morphisms of
`𝒪_U`-modules. -/
@[reassoc]
theorem cocone_naturality_hom {I : Type w} [Category.{v} I] {D : I ⥤ QuasicoherentModule B S hS G}
    {M : QuasicoherentModule B S hS G} (φ : D ⟶ (Functor.const I).obj M) {i j : I} (g : i ⟶ j) :
    Hom.hom (M := D.obj i) (N := D.obj j) (D.map g) ≫ Hom.hom (M := D.obj j) (N := M) (φ.app j) =
      Hom.hom (M := D.obj i) (N := M) (φ.app i) :=
  (congrArg Hom.hom (φ.naturality g)).trans (Category.comp_id _)

/-- **A cocone of quasi-coherent modules on a groupoid in algebraic spaces is colimiting as soon
as its underlying cocone of `𝒪_U`-modules is.**  The descended morphism of underlying modules is
compatible with the transition morphisms because the inverse image along the target preserves the
colimit, being a left adjoint, so two morphisms out of `t^*` of the vertex agree as soon as they
agree on every leg. -/
def isColimitOfUnderlying {I : Type w} [Category.{v} I] {D : I ⥤ QuasicoherentModule B S hS G}
    (c : Cocone D) (hc : IsColimit ((forget G).mapCocone c)) : IsColimit c := by
  have hct : IsColimit ((modulePullback B S hS G.target).mapCocone ((forget G).mapCocone c)) :=
    isColimitOfPreserves (modulePullback B S hS G.target) hc
  refine
    { desc := fun s =>
        { hom := hc.desc ((forget G).mapCocone s)
          comm := ?_ }
      fac := fun s i => Hom.ext (hc.fac ((forget G).mapCocone s) i)
      uniq := fun s m hm => Hom.ext (hc.uniq ((forget G).mapCocone s) m.hom
        fun i => congrArg Hom.hom (hm i)) }
  refine hct.hom_ext fun i => ?_
  have hfac : (c.ι.app i).hom ≫ hc.desc ((forget G).mapCocone s) = (s.ι.app i).hom :=
    hc.fac ((forget G).mapCocone s) i
  change (modulePullback B S hS G.target).map (c.ι.app i).hom ≫ c.pt.alpha ≫
      (modulePullback B S hS G.source).map (hc.desc ((forget G).mapCocone s)) =
    (modulePullback B S hS G.target).map (c.ι.app i).hom ≫
      (modulePullback B S hS G.target).map (hc.desc ((forget G).mapCocone s)) ≫ s.pt.alpha
  have hcommc : (D.obj i).alpha ≫ (modulePullback B S hS G.source).map (c.ι.app i).hom =
      (modulePullback B S hS G.target).map (c.ι.app i).hom ≫ c.pt.alpha := (c.ι.app i).comm
  have hcomms : (D.obj i).alpha ≫ (modulePullback B S hS G.source).map (s.ι.app i).hom =
      (modulePullback B S hS G.target).map (s.ι.app i).hom ≫ s.pt.alpha := (s.ι.app i).comm
  rw [← Category.assoc, ← hcommc, Category.assoc, ← Functor.map_comp, hfac, hcomms,
    ← Category.assoc,
    ← Functor.map_comp, hfac]

/-- **A filtered diagram of submodules exhausting a quasi-coherent module on the groupoid has it
as its colimit.**  Let `φ : D ⟶ M` be a cocone over an essentially small filtered category whose
legs are monomorphisms of the underlying `𝒪_U`-modules and whose images have supremum `⊤`.  Then
it is a colimit cocone: on the underlying modules this is the description of a directed union of
subobjects in a Grothendieck abelian category as its colimit, and
`AlgebraicGeometry.Space.QuasicoherentModule.isColimitOfUnderlying` lifts it to the groupoid. -/
def isColimit_of_iSup_eq_top {I : Type w} [Category.{v} I] [EssentiallySmall.{u} I] [IsFiltered I]
    {D : I ⥤ QuasicoherentModule B S hS G} {M : QuasicoherentModule B S hS G}
    (φ : D ⟶ (Functor.const I).obj M)
    (hmono : ∀ i, Mono (Hom.hom (M := D.obj i) (N := M) (φ.app i)))
    (hsup : letI := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
      (⨆ i, imageSubobject (Hom.hom (M := D.obj i) (N := M) (φ.app i))) = ⊤) :
    IsColimit (Cocone.mk M φ) := by
  letI := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
  refine isColimitOfUnderlying _ ?_
  let e := equivSmallModel.{u} I
  have : IsFiltered (SmallModel.{u} I) := IsFiltered.of_equivalence e
  let P : SmallModel.{u} I ⥤ MonoOver M.F.obj :=
    { obj := fun j => MonoOver.mk (hf := hmono (e.inverse.obj j))
        (Hom.hom (M := D.obj (e.inverse.obj j)) (N := M) (φ.app (e.inverse.obj j)))
      map := fun {j j'} g => MonoOver.homMk (D.map (e.inverse.map g)).hom
        (cocone_naturality_hom φ (e.inverse.map g))
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  let c : Cocone (P ⋙ MonoOver.forget _) :=
    Cocone.mk (Over.mk (𝟙 M.F.obj))
      { app := fun j => Over.homMk (Hom.hom (M := D.obj (e.inverse.obj j)) (N := M)
          (φ.app (e.inverse.obj j))) (by simp [P])
        naturality := fun {j j'} g => Over.OverMorphism.ext
          ((cocone_naturality_hom φ (e.inverse.map g)).trans (Category.comp_id _).symm) }
  have : Mono c.pt.hom := inferInstanceAs (Mono (𝟙 M.F.obj))
  have himg : ∀ i, imageSubobject (Hom.hom (M := D.obj i) (N := M) (φ.app i)) =
      @Subobject.mk _ _ _ _ (Hom.hom (M := D.obj i) (N := M) (φ.app i)) (hmono i) := fun i => by
    have := hmono i
    exact imageSubobject_mono _
  have hs : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (P.obj j).obj.hom := by
    change Subobject.mk (𝟙 M.F.obj) = ⨆ j, @Subobject.mk _ _ _ _
      (Hom.hom (M := D.obj (e.inverse.obj j)) (N := M) (φ.app (e.inverse.obj j)))
      (hmono (e.inverse.obj j))
    rw [Subobject.mk_eq_top_of_isIso, ← hsup]
    refine le_antisymm (iSup_le fun i => ?_)
      (iSup_le fun j => le_iSup_of_le (e.inverse.obj j) (himg _).ge)
    have := hmono i
    have := hmono (e.inverse.obj (e.functor.obj i))
    rw [himg i]
    exact le_iSup_of_le (e.functor.obj i) (Subobject.mk_le_mk_of_comm
      (D.map (e.unitIso.hom.app i)).hom (cocone_naturality_hom φ (e.unitIso.hom.app i)))
  have hc := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup P c hs
  have hc' : IsColimit (((forget G).mapCocone (Cocone.mk M φ)).whisker e.inverse) :=
    IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) (fun j => Category.comp_id _))
  exact IsColimit.ofWhiskerEquivalence e.symm hc'

/-! ### Every coherent submodule lies in some `ℱ ∩ s_*t^*ℋ` -/

attribute [local instance] isIso_alpha

/-- **Every coherent submodule `ℋ` of `ℱ` lies in `ℱ ∩ s_*t^*ℋ'` for some coherent submodule
`ℋ'` of `ℱ`.**  Here `ℱ ∩ s_*t^*ℋ'` is formed for `t^*ℋ' ⟶ t^*ℱ ⟶ s^*ℱ`, the inverse image of
the inclusion followed by the transition morphism `β`, and `U`, `R` are Noetherian and `t` is
flat.

The image `𝒦` of `s^*ℋ ⟶ s^*ℱ ⟶ t^*ℱ`, the second map being `β⁻¹`, is a coherent submodule of
`t^*ℱ` on the Noetherian space `R`.  By Stacks 07UV `ℱ` is the filtered colimit of its coherent
submodules `ℋ'`, so `t^*ℱ` is the directed union of the `t^*ℋ'`, the inverse image `t^*` being a
left adjoint and, `t` being flat, preserving monomorphisms.  By the ascending chain condition on
`R` the coherent `𝒦` lies in one `t^*ℋ'`, which says that `s^*ℋ ⟶ s^*ℱ` factors through
`t^*ℋ' ⟶ s^*ℱ`; by adjunction `ℋ ⟶ ℱ` factors through `ℱ ∩ s_*t^*ℋ'`. -/
theorem exists_le_intersectionPushforward (hZ : B.Contains (⊤_ Scheme.{u}))
    (hU : IsNoetherian B S hS hZ G.objects.1) (hR : IsNoetherian B S hS hZ G.arrows.1)
    (ht : IsFlat B S hS G.target.hom) (M : QuasicoherentModule B S hS G)
    (H : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj) :
    ∃ (H' : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj)
      (m : (H.obj : Modules.{u, u} B S hS G.objects.1 G.objects.2) ⟶
        intersectionPushforward B S hS G.source
          ((modulePullback B S hS G.target).map H'.obj.arrow ≫ M.alpha)),
      m ≫ intersectionPushforwardι B S hS G.source
        ((modulePullback B S hS G.target).map H'.obj.arrow ≫ M.alpha) = H.obj.arrow := by
  classical
  have := isGrothendieckAbelian_modules B S hS G.arrows.1 G.arrows.2
  have := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
  have : Fact (HasEtaleLocalProperty B S hS G.arrows.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hR.2.2⟩
  have : Fact (HasEtaleLocalProperty B S hS G.objects.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hU.2.2⟩
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.target ht
  have : M.F.obj.IsQuasicoherentOnSite := M.F.property
  let T := modulePullback B S hS G.target
  have hTF : (T.obj M.F.obj).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS G.target M.F.obj
      M.F.property
  -- the coherent image `𝒦` of `s^*ℋ ⟶ s^*ℱ ⟶ t^*ℱ`
  let κ : (modulePullback B S hS G.source).obj (H.obj : Modules.{u, u} B S hS G.objects.1
      G.objects.2) ⟶ T.obj M.F.obj :=
    (modulePullback B S hS G.source).map H.obj.arrow ≫ inv M.alpha
  let K : Subobject (T.obj M.F.obj) := imageSubobject κ
  have hK : IsCoherent B S hS G.arrows.1 G.arrows.2 (K : Modules.{u, u} B S hS G.arrows.1
      G.arrows.2) :=
    isCoherent_imageSubobject B S hS G.arrows.1 G.arrows.2 κ
      (isCoherent_modulePullback B S hS G.source _ H.property) hTF
  -- the directed family of the `t^*ℋ'`, over a small model of the coherent submodules
  let I := CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj
  have : IsFiltered I := isFiltered_coherentSubobject B S hS _ _ M.F.obj
  obtain ⟨-, ⟨hcol⟩⟩ := isFiltered_and_nonempty_isColimit_coherentSubobjectCocone hZ hU M.F.obj
  let e := equivSmallModel.{u} I
  have : IsFiltered (SmallModel.{u} I) := IsFiltered.of_equivalence e
  have : T.PreservesMonomorphisms := inferInstance
  have hm : ∀ H' : I, Mono (T.map H'.obj.arrow) := fun _ => T.map_mono _
  let s : SmallModel.{u} I → Subobject (T.obj M.F.obj) :=
    fun j => Subobject.mk (T.map (e.inverse.obj j).obj.arrow)
  have hs : ∀ {i j : SmallModel.{u} I}, (i ⟶ j) → s i ≤ s j := fun {i j} g =>
    Subobject.mk_le_mk_of_comm (T.map (Subobject.underlying.map (e.inverse.map g).hom)) (by
      rw [← T.map_comp, Subobject.underlying_arrow])
  have hqc : ∀ j, (s j : Modules.{u, u} B S hS G.arrows.1 G.arrows.2).IsQuasicoherentOnSite :=
    fun j => (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      (Subobject.underlyingIso _).symm
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS G.target _
        (e.inverse.obj j).property.toIsQuasicoherentOnSite)
  have hcolS : IsColimit ((T.mapCocone (coherentSubobjectCocone B S hS G.objects.1 G.objects.2
      M.F.obj)).whisker e.inverse) :=
    (isColimitOfPreserves T hcol).whiskerEquivalence e.symm
  have htop := iSup_imageSubobject_eq_top_of_isColimit _ hcolS
  have hsup : (⨆ j, s j) = ⊤ := by
    refine eq_top_iff.2 (le_of_eq_of_le htop.symm ?_)
    exact iSup_le fun j => le_iSup_of_le j
      (@imageSubobject_mono _ _ _ _ (T.map (e.inverse.obj j).obj.arrow) (hm _)).le
  obtain ⟨j, hj⟩ := exists_le_of_le_iSup_of_isCoherent B S hS G.arrows.1 G.arrows.2 hZ hR hTF
    K hK s hs hqc (hsup ▸ le_top)
  refine ⟨e.inverse.obj j, intersectionPushforwardLift B S hS G.source _ H.obj.arrow
    (factorThruImageSubobject κ ≫ Subobject.ofLEMk K _ hj) ?_,
    intersectionPushforwardLift_ι B S hS G.source _ _ _ _⟩
  rw [Category.assoc, ← Category.assoc (Subobject.ofLEMk _ _ _), Subobject.ofLEMk_comp,
    imageSubobject_arrow_comp_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-! ### `ℱ ∩ s_*t^*ℋ` as a fibre product over `s_*t^*ℱ` -/

/-- **The fibre product of `ℱ ⟶ s_*t^*ℱ ⟵ s_*t^*ℋ` is `ℱ ∩ s_*t^*ℋ`.**  The left arrow is the
composite `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ` of the unit and of `s_*β⁻¹`, and the right one is
`s_*t^*` of a morphism `ι : ℋ ⟶ ℱ`.  Composing both arrows with the isomorphism `s_*β` turns the
cospan into `ℱ ⟶ s_*s^*ℱ ⟵ s_*t^*ℋ`, the unit and `s_*` of `t^*ℋ ⟶ t^*ℱ ⟶ s^*ℱ`, which is the
cospan defining `ℱ ∩ s_*t^*ℋ` of Stacks 0GPR. -/
theorem isPullback_unit_of_isPullback_sourceUnitInvAlpha (M : QuasicoherentModule B S hS G)
    {H : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj)
    {P : Modules.{u, u} B S hS G.objects.1 G.objects.2} {p₁ : P ⟶ M.F.obj}
    {p₂ : P ⟶ (modulePushforward B S hS G.source).obj
      ((modulePullback B S hS G.target).obj H)}
    (h : IsPullback p₁ p₂ (sourceUnitInvAlpha M)
      ((modulePushforward B S hS G.source).map ((modulePullback B S hS G.target).map ι))) :
    IsPullback p₁ p₂ (pullbackPushforwardUnit B S hS G.source M.F.obj)
      ((modulePushforward B S hS G.source).map
        ((modulePullback B S hS G.target).map ι ≫ M.alpha)) := by
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((modulePushforward B S hS G.source).mapIso (asIso M.alpha)) ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Functor.mapIso_hom, asIso_hom, sourceUnitInvAlpha, Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Functor.mapIso_hom, asIso_hom, ← Functor.map_comp, Iso.refl_hom, Category.id_comp]

/-- The comparison of a fibre product of `ℱ ⟶ s_*t^*ℱ ⟵ s_*t^*ℋ` with `ℱ ∩ s_*t^*ℋ`, given by
`AlgebraicGeometry.Space.QuasicoherentModule.isPullback_unit_of_isPullback_sourceUnitInvAlpha`;
it commutes with the two maps to `ℱ`. -/
theorem exists_iso_intersectionPushforward (M : QuasicoherentModule B S hS G)
    {H : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj)
    {P : Modules.{u, u} B S hS G.objects.1 G.objects.2} {p₁ : P ⟶ M.F.obj}
    {p₂ : P ⟶ (modulePushforward B S hS G.source).obj
      ((modulePullback B S hS G.target).obj H)}
    (h : IsPullback p₁ p₂ (sourceUnitInvAlpha M)
      ((modulePushforward B S hS G.source).map ((modulePullback B S hS G.target).map ι))) :
    ∃ e : P ≅ intersectionPushforward B S hS G.source
        ((modulePullback B S hS G.target).map ι ≫ M.alpha),
      e.hom ≫ intersectionPushforwardι B S hS G.source
        ((modulePullback B S hS G.target).map ι ≫ M.alpha) = p₁ :=
  ⟨(isPullback_unit_of_isPullback_sourceUnitInvAlpha M ι h).isoPullback,
    (isPullback_unit_of_isPullback_sourceUnitInvAlpha M ι h).isoPullback_hom_fst⟩

/-! ### Comparing submodules on the groupoid through their underlying modules -/

/-- **Containment of submodules on the groupoid is detected on the underlying modules**, when the
source is flat and the larger submodule is injective on underlying modules.  A factorization `k`
of the underlying inclusions is compatible with the transition morphisms: after composing with the
monomorphism `s^*` of the larger inclusion both sides become `t^*` of the smaller inclusion
followed by the transition morphism of the ambient module. -/
theorem subobject_le_of_comm (hs : IsFlat B S hS G.source.hom) {M : QuasicoherentModule B S hS G}
    (P Q : Subobject M)
    (hQ : Mono (Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow))
    (k : (P : QuasicoherentModule B S hS G).F.obj ⟶ (Q : QuasicoherentModule B S hS G).F.obj)
    (hk : k ≫ Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow =
      Hom.hom (M := (P : QuasicoherentModule B S hS G)) (N := M) P.arrow) : P ≤ Q := by
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.source hs
  have hmono : Mono ((modulePullback B S hS G.source).map
      (Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow)) :=
    (modulePullback B S hS G.source).map_mono _
  refine Subobject.le_of_comm ⟨k, ?_⟩ (Hom.ext hk)
  rw [← cancel_mono ((modulePullback B S hS G.source).map
      (Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow)),
    Category.assoc, ← Functor.map_comp, hk, Category.assoc, Q.arrow.comm, ← Category.assoc,
    ← Functor.map_comp, hk]
  exact P.arrow.comm

variable (B S hS) in
/-- The morphism `t^*ℋ ⟶ t^*ℱ ⟶ s^*ℱ` of a submodule `ℋ ⊆ ℱ`, for a quasi-coherent module
`(ℱ, β)` on the groupoid: the inverse image along the target of the inclusion followed by the
transition morphism. -/
abbrev transitionInclusion (M : QuasicoherentModule B S hS G)
    {H : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj) :
    (modulePullback B S hS G.target).obj H ⟶ (modulePullback B S hS G.source).obj M.F.obj :=
  (modulePullback B S hS G.target).map ι ≫ M.alpha

/-- For `t` flat, the inverse image along the target preserves monomorphisms. -/
private theorem mono_modulePullback_target_map (ht : IsFlat B S hS G.target.hom)
    {F H : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ F) [Mono ι] :
    Mono ((modulePullback B S hS G.target).map ι) :=
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.target ht
  (modulePullback B S hS G.target).map_mono _

/-- **`ℱ ∩ s_*t^*ℋ` is coherent** for a coherent submodule `ℋ` of `ℱ`, when `U` and `R` are
locally Noetherian and `s` is flat, quasi-compact and quasi-separated and `t` is flat.  This is
Stacks 0GPR for `f = s`, `𝒢 = t^*ℋ` and `φ : t^*ℋ ⟶ t^*ℱ ⟶ s^*ℱ`: the morphism `φ` is injective
because `t` is flat, `s` is surjective because the unit is a section of it, and `t^*ℋ` is
coherent as the inverse image of a coherent module onto a locally Noetherian space. -/
theorem isCoherent_intersectionPushforward_transitionInclusion
    (hU : HasEtaleLocalProperty B S hS G.objects.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hR : HasEtaleLocalProperty B S hS G.arrows.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hs : IsFlat B S hS G.source.hom) (hsqc : IsQuasiCompact B S hS G.source.hom)
    (hsqs : IsQuasiSeparated B S hS G.source.hom) (ht : IsFlat B S hS G.target.hom)
    (M : QuasicoherentModule B S hS G)
    (H : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj) :
    IsCoherent B S hS G.objects.1 G.objects.2
      (intersectionPushforward B S hS G.source (transitionInclusion B S hS M H.obj.arrow)) := by
  have : Fact (HasEtaleLocalProperty B S hS G.arrows.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hR⟩
  have : Mono ((modulePullback B S hS G.target).map H.obj.arrow) :=
    mono_modulePullback_target_map ht _
  exact isCoherent_intersectionPushforward B S hS G.source M.F.obj _ _ (mono_comp _ _) hsqc hsqs hs
    (Stack.QuotientAtlas.isSurjective_source G) hU hR M.F.property
    (isCoherent_modulePullback B S hS G.target _ H.property)

/-! ### Fibre products on the groupoid -/

open GroupoidInAlgebraicSpaces in
/-- **Fibre products of quasi-coherent modules on the groupoid, for `s` flat, are computed on the
underlying modules.**  The fibre product of the underlying modules is quasi-coherent, and it
carries a transition morphism because the inverse images along `s`, along `c ≫ s` and along
`e ≫ s` are left exact: `s` is flat, `c` is a base change of `s` by Stacks 043Z, and `e ≫ s` is
the identity. -/
theorem exists_isPullback_of_isFlat (hs : IsFlat B S hS G.source.hom)
    {X Y Z : QuasicoherentModule B S hS G} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃ (P : QuasicoherentModule B S hS G) (p₁ : P ⟶ X) (p₂ : P ⟶ Y),
      IsPullback p₁ p₂ f g ∧ IsPullback p₁.hom p₂.hom f.hom g.hom := by
  have hcomp : IsFlat B S hS G.comp.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback (Space.isPullback_comp_source G).flip hs
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.source hs
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (G.comp ≫ G.source)
    (isFlat_comp B S hS (AlgebraicSpaces.fiberProduct B S hS G.source G.target).2 G.arrows.2
      G.objects.2 G.comp.hom G.source.hom hcomp hs)
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (identityArrow G ≫ G.source)
    (by rw [identityArrow_comp_source]; exact isFlat_id B S hS G.objects.2)
  let c : Cone (cospan f g ⋙ forget G) :=
    (Cone.postcompose (cospanCompIso (forget G) f g).inv).obj (pullback.cone f.hom g.hom)
  have hc : IsLimit c :=
    (IsLimit.postcomposeInvEquiv (cospanCompIso (forget G) f g) _).symm
      (pullback.isLimit f.hom g.hom)
  have hqc : c.pt.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isPullback B S hS _ _ (IsPullback.of_hasPullback f.hom g.hom)
      X.F.property Y.F.property Z.F.property
  let L := liftedLimitCone (cospan f g) c hc hqc
  refine ⟨L.pt, L.π.app .left, L.π.app .right,
    IsPullback.of_isLimit (c := L) (liftedLimitConeIsLimit (cospan f g) c hc hqc), ?_⟩
  rw [show (L.π.app .left).hom = pullback.fst f.hom g.hom from Category.comp_id _,
    show (L.π.app .right).hom = pullback.snd f.hom g.hom from Category.comp_id _]
  exact IsPullback.of_hasPullback f.hom g.hom

/-- A morphism of quasi-coherent modules on the groupoid whose underlying morphism of
`𝒪_U`-modules is a monomorphism is a monomorphism. -/
theorem mono_of_mono_hom {X Y : QuasicoherentModule B S hS G} (f : X ⟶ Y) (hf : Mono f.hom) :
    Mono f :=
  ⟨fun _ _ hgh => Hom.ext ((cancel_mono f.hom).1 (congrArg Hom.hom hgh))⟩

/-- **A fibre product over `s_*t^*ℱ` on the groupoid is a submodule with underlying module
`ℱ ∩ s_*t^*ℋ`.**  Let `p₁ : P ⟶ (ℱ, β)` be a morphism on the groupoid whose underlying morphism
is the first projection of a fibre product of `ℱ ⟶ s_*t^*ℱ ⟵ s_*t^*ℋ`, the left arrow being the
unit followed by `s_*β⁻¹`.  Then `p₁` is injective as soon as `ℋ ⟶ ℱ` is and `t` is flat, and the
submodule it defines has underlying module `ℱ ∩ s_*t^*ℋ`, compatibly with the inclusions
into `ℱ`. -/
theorem exists_subobject_of_isPullback (ht : IsFlat B S hS G.target.hom)
    (M : QuasicoherentModule B S hS G) {P : QuasicoherentModule B S hS G} (p₁ : P ⟶ M)
    {H : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj) [Mono ι]
    {p₂ : P.F.obj ⟶ (modulePushforward B S hS G.source).obj
      ((modulePullback B S hS G.target).obj H)}
    (h : IsPullback p₁.hom p₂ (sourceUnitInvAlpha M)
      ((modulePushforward B S hS G.source).map ((modulePullback B S hS G.target).map ι))) :
    ∃ (Q : Subobject M) (e : (Q : QuasicoherentModule B S hS G).F.obj ≅
        intersectionPushforward B S hS G.source (transitionInclusion B S hS M ι)),
      e.hom ≫ intersectionPushforwardι B S hS G.source (transitionInclusion B S hS M ι) =
        Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow := by
  have : Mono ((modulePullback B S hS G.target).map ι) :=
    mono_modulePullback_target_map ht _
  have : Mono ((modulePushforward B S hS G.source).map
      ((modulePullback B S hS G.target).map ι)) :=
    mono_modulePushforward_map B S hS G.source _ inferInstance
  have : Mono p₁.hom := h.mono_fst_of_mono
  have := mono_of_mono_hom p₁ inferInstance
  obtain ⟨e, he⟩ := exists_iso_intersectionPushforward M ι h
  refine ⟨Subobject.mk p₁, (forget G).mapIso (Subobject.underlyingIso p₁) ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he]
  exact congrArg Hom.hom (Subobject.underlyingIso_hom_comp_eq_mk p₁)

/-! ### The colimit bookkeeping -/

/-- A submodule of `(ℱ, β)` on the groupoid whose underlying submodule is `ℱ ∩ s_*t^*ℋ` is
injective on underlying modules, for `t` flat and `ℋ ⊆ ℱ`. -/
theorem mono_arrow_hom_of_iso_intersectionPushforward (ht : IsFlat B S hS G.target.hom)
    {M : QuasicoherentModule B S hS G} {H : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    (ι : H ⟶ M.F.obj) [Mono ι] (Q : Subobject M)
    (e : (Q : QuasicoherentModule B S hS G).F.obj ≅
      intersectionPushforward B S hS G.source (transitionInclusion B S hS M ι))
    (he : e.hom ≫ intersectionPushforwardι B S hS G.source (transitionInclusion B S hS M ι) =
      Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow) :
    Mono (Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow) := by
  have : Mono ((modulePullback B S hS G.target).map ι) :=
    mono_modulePullback_target_map ht _
  have : Mono (intersectionPushforwardι B S hS G.source (transitionInclusion B S hS M ι)) :=
    mono_intersectionPushforwardι B S hS G.source _ (mono_comp _ _)
  rw [← he]
  exact mono_comp _ _

/-- **`ℋ ↦ ℱ ∩ s_*t^*ℋ` is monotone on submodules on the groupoid.**  If `Q` and `Q'` are
submodules of `(ℱ, β)` on the groupoid with underlying submodules `ℱ ∩ s_*t^*ℋ` and
`ℱ ∩ s_*t^*ℋ'`, and `ℋ ⊆ ℋ'`, then `Q ⊆ Q'`, for `s` and `t` flat. -/
theorem le_of_iso_intersectionPushforward (hs : IsFlat B S hS G.source.hom)
    (ht : IsFlat B S hS G.target.hom) {M : QuasicoherentModule B S hS G}
    {H H' : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj) (ι' : H' ⟶ M.F.obj)
    [Mono ι'] (k : H ⟶ H') (hk : k ≫ ι' = ι) (Q Q' : Subobject M)
    (e : (Q : QuasicoherentModule B S hS G).F.obj ≅
      intersectionPushforward B S hS G.source (transitionInclusion B S hS M ι))
    (he : e.hom ≫ intersectionPushforwardι B S hS G.source (transitionInclusion B S hS M ι) =
      Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow)
    (e' : (Q' : QuasicoherentModule B S hS G).F.obj ≅
      intersectionPushforward B S hS G.source (transitionInclusion B S hS M ι'))
    (he' : e'.hom ≫ intersectionPushforwardι B S hS G.source (transitionInclusion B S hS M ι') =
      Hom.hom (M := (Q' : QuasicoherentModule B S hS G)) (N := M) Q'.arrow) :
    Q ≤ Q' := by
  refine subobject_le_of_comm hs Q Q'
    (mono_arrow_hom_of_iso_intersectionPushforward ht ι' Q' e' he')
    (e.hom ≫ intersectionPushforwardMap B S hS G.source _ _
      ((modulePullback B S hS G.target).map k) ?_ ≫ e'.inv) ?_
  · rw [transitionInclusion, ← Category.assoc, ← Functor.map_comp, hk]
  · rw [Category.assoc, Category.assoc, ← he', Iso.inv_hom_id_assoc,
      intersectionPushforwardMap_ι, he]

/-- **The submodules `ℱ ∩ s_*t^*ℋ` on the groupoid exhaust `(ℱ, β)`.**  Let `U` and `R` be
Noetherian and `t` flat, and let `P ℋ` be a submodule of `(ℱ, β)` on the groupoid with
underlying submodule `ℱ ∩ s_*t^*ℋ`, for every coherent submodule `ℋ` of `ℱ`.  Then the
underlying submodules of the `P ℋ` have supremum `ℱ`: every coherent `ℋ` lies in some
`ℱ ∩ s_*t^*ℋ'`, by `exists_le_intersectionPushforward`, and the coherent submodules exhaust `ℱ`
by Stacks 07UV. -/
theorem iSup_imageSubobject_eq_top_of_iso_intersectionPushforward
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hU : IsNoetherian B S hS hZ G.objects.1) (hR : IsNoetherian B S hS hZ G.arrows.1)
    (ht : IsFlat B S hS G.target.hom) (M : QuasicoherentModule B S hS G)
    (P : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj → Subobject M)
    (e : ∀ H, (P H : QuasicoherentModule B S hS G).F.obj ≅
      intersectionPushforward B S hS G.source (transitionInclusion B S hS M H.obj.arrow))
    (he : ∀ H, (e H).hom ≫ intersectionPushforwardι B S hS G.source
        (transitionInclusion B S hS M H.obj.arrow) =
      Hom.hom (M := (P H : QuasicoherentModule B S hS G)) (N := M) (P H).arrow) :
    letI := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
    (⨆ H, imageSubobject (Hom.hom (M := (P H : QuasicoherentModule B S hS G)) (N := M)
      (P H).arrow)) = ⊤ := by
  have := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
  have : Fact (HasEtaleLocalProperty B S hS G.objects.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hU.2.2⟩
  let I := CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj
  have : IsFiltered I := isFiltered_coherentSubobject B S hS _ _ M.F.obj
  have hHtop : (⨆ H : I, H.obj) = ⊤ := by
    obtain ⟨-, ⟨hcol⟩⟩ := isFiltered_and_nonempty_isColimit_coherentSubobjectCocone hZ hU M.F.obj
    let eI := equivSmallModel.{u} I
    have htop := iSup_imageSubobject_eq_top_of_isColimit _ (hcol.whiskerEquivalence eI.symm)
    refine eq_top_iff.2 (le_of_eq_of_le htop.symm (iSup_le fun j =>
      le_iSup_of_le (eI.inverse.obj j) ?_))
    change imageSubobject (eI.inverse.obj j).obj.arrow ≤ (eI.inverse.obj j).obj
    rw [imageSubobject_mono, Subobject.mk_arrow]
  refine eq_top_iff.2 (hHtop.symm.le.trans (iSup_le fun H₀ => ?_))
  obtain ⟨H', m, hm⟩ := exists_le_intersectionPushforward hZ hU hR ht M H₀
  refine le_iSup_of_le H' ?_
  have := mono_arrow_hom_of_iso_intersectionPushforward ht H'.obj.arrow (P H') (e H') (he H')
  rw [imageSubobject_mono]
  refine Subobject.le_mk_of_comm (m ≫ (e H').inv) ?_
  rw [Category.assoc, ← he H', Iso.inv_hom_id_assoc, hm]

/-! ### The right adjoint of the forgetful functor on underlying modules -/

/-- The underlying morphism of a direct image along a morphism of groupoids, after a functor into
the quasi-coherent modules on the source groupoid. -/
theorem comp_groupoidQuasicoherentPushforward_map_hom {G₁ : GroupoidInAlgebraicSpaces B S hS A}
    (φ : GroupoidInAlgebraicSpaces.Hom G₁ G) (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
    (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
    (hpb : IsPullback φ.arrowsMap G₁.target G.target φ.objectsMap)
    (hsflat : IsFlat B S hS G.source.hom) {C : Type*} [Category C]
    (K : C ⥤ QuasicoherentModule B S hS G₁) {X Y : C} (ψ : X ⟶ Y) :
    ((K ⋙ groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).map ψ).hom =
      (modulePushforward B S hS φ.objectsMap).map (K.map ψ).hom :=
  rfl

/-- A fibre product over `ℱ ⟶ s_*t^*ℱ` read through any typing of the source and the target of
the groupoid: the unit followed by `s_*β⁻¹`, and `s_*t^*` of a morphism into `ℱ`, in the typing in
which they are given, are those of the groupoid. -/
theorem isPullback_sourceUnitInvAlpha_of_heq (M : QuasicoherentModule B S hS G)
    {Y : AlgebraicSpaces B S hS} (hY : Y = G.arrows) (s t : Y ⟶ G.objects)
    (hs : HEq s G.source) (ht : HEq t G.target)
    {H P : Modules.{u, u} B S hS G.objects.1 G.objects.2} (ι : H ⟶ M.F.obj) {p₁ : P ⟶ M.F.obj}
    {p₂ : P ⟶ (modulePushforward B S hS s).obj ((modulePullback B S hS t).obj H)}
    {a : M.F.obj ⟶ (modulePushforward B S hS s).obj ((modulePullback B S hS t).obj M.F.obj)}
    (ha : HEq a (sourceUnitInvAlpha M))
    (h : IsPullback p₁ p₂ a ((modulePushforward B S hS s).map ((modulePullback B S hS t).map ι))) :
    ∃ p₂' : P ⟶ (modulePushforward B S hS G.source).obj
        ((modulePullback B S hS G.target).obj H),
      IsPullback p₁ p₂' (sourceUnitInvAlpha M)
        ((modulePushforward B S hS G.source).map ((modulePullback B S hS G.target).map ι)) := by
  subst hY
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq ha
  exact ⟨p₂, h⟩

/-- **Stacks 0GPS.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` such that
`U` and `R` are Noetherian and `s` and `t` are flat, quasi-compact and quasi-separated.  Then every
quasi-coherent module `(ℱ, β)` on `(U, R, s, t, c)` is a filtered colimit of coherent modules: it
is the colimit of a diagram, indexed by a filtered category, of quasi-coherent modules on
`(U, R, s, t, c)` whose underlying `𝒪_U`-modules are coherent.

The diagram is indexed by the coherent submodules `ℋ` of `ℱ`, and its term at `ℋ` is the fibre
product of the unit `(ℱ, β) ⟶ (s_*t^*ℱ, α)` of Stacks 0GPP with `(s_*t^*ℋ, α) ⟶ (s_*t^*ℱ, α)`.
By the description of the unit in Stacks 0GPQ its underlying module is `ℱ ∩ s_*t^*ℋ`, which is
coherent by Stacks 0GPR. -/
@[stacks 0GPS]
theorem exists_filtered_diagram_isCoherent (terminal_mem : B.Contains (⊤_ Scheme.{u}))
    (objects_noetherian : IsNoetherian B S hS terminal_mem G.objects.1)
    (arrows_noetherian : IsNoetherian B S hS terminal_mem G.arrows.1)
    (source_flat : IsFlat B S hS G.source.hom)
    (source_quasiCompact : IsQuasiCompact B S hS G.source.hom)
    (source_quasiSeparated : IsQuasiSeparated B S hS G.source.hom)
    (target_flat : IsFlat B S hS G.target.hom)
    (_target_quasiCompact : IsQuasiCompact B S hS G.target.hom)
    (_target_quasiSeparated : IsQuasiSeparated B S hS G.target.hom)
    (M : QuasicoherentModule B S hS G) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ QuasicoherentModule B S hS G) (φ : D ⟶ (Functor.const I).obj M),
      (∀ i, IsCoherent B S hS G.objects.1 G.objects.2 (D.obj i).F.obj) ∧
        Nonempty (IsColimit (Cocone.mk M φ)) := by
  classical
  have hsub : ∀ H : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj,
      ∃ (Q : Subobject M) (e : (Q : QuasicoherentModule B S hS G).F.obj ≅
          intersectionPushforward B S hS G.source (transitionInclusion B S hS M H.obj.arrow)),
        e.hom ≫ intersectionPushforwardι B S hS G.source
            (transitionInclusion B S hS M H.obj.arrow) =
          Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow := by
    intro H
    let adj := forgetAdjunction G source_flat source_quasiCompact source_quasiSeparated
    let Hq : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property :=
      ⟨H.obj, H.property.toIsQuasicoherentOnSite⟩
    let ι : Hq ⟶ (forgetQuasicoherent G).obj M := ObjectProperty.homMk H.obj.arrow
    obtain ⟨P, p₁, p₂, -, hP⟩ := exists_isPullback_of_isFlat source_flat (adj.unit.app M)
      ((cofree G source_flat source_quasiCompact source_quasiSeparated).map ι)
    have hmap : ((cofree G source_flat source_quasiCompact source_quasiSeparated).map ι).hom =
        (modulePushforward B S hS (GroupoidInAlgebraicSpaces.targetPairsHom G).objectsMap).map
          ((targetPairsBase G).map ι).hom :=
      comp_groupoidQuasicoherentPushforward_map_hom
        (GroupoidInAlgebraicSpaces.targetPairsHom G) source_quasiCompact source_quasiSeparated
        (GroupoidInAlgebraicSpaces.isPullback_targetPairsHom G) source_flat (targetPairsBase G) ι
    rw [hmap, quasicoherentFromSpaceBase_map, spaceBaseHom_hom, spaceBasePullbackMap_eq] at hP
    obtain ⟨p₂', hP'⟩ := isPullback_sourceUnitInvAlpha_of_heq M
      (Y := (GroupoidInAlgebraicSpaces.targetPairsGroupoid G).objects) rfl
      (GroupoidInAlgebraicSpaces.targetPairsHom G).objectsMap
      (G.target : (GroupoidInAlgebraicSpaces.targetPairsGroupoid G).objects ⟶ G.objects)
      HEq.rfl HEq.rfl H.obj.arrow
      (heq_of_eq (forgetAdjunction_unit_app_hom G source_flat source_quasiCompact
        source_quasiSeparated M)) hP
    exact exists_subobject_of_isPullback target_flat M p₁ H.obj.arrow hP'
  choose P e he using hsub
  have := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
  let I := CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj
  have : Fact (HasEtaleLocalProperty B S hS G.objects.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨objects_noetherian.2.2⟩
  have : IsFiltered I := isFiltered_coherentSubobject B S hS _ _ M.F.obj
  have hPle : ∀ {H H' : I}, (H ⟶ H') → P H ≤ P H' := fun {H H'} g =>
    le_of_iso_intersectionPushforward source_flat target_flat H.obj.arrow H'.obj.arrow
      (Subobject.underlying.map g.hom) (Subobject.underlying_arrow g.hom) (P H) (P H') (e H)
      (he H) (e H') (he H')
  let D : I ⥤ QuasicoherentModule B S hS G :=
    { obj := fun H => (P H : QuasicoherentModule B S hS G)
      map := fun g => Subobject.underlying.map (homOfLE (hPle g))
      map_id := fun _ => by
        rw [← Subobject.underlying.map_id]
        exact congrArg _ (Subsingleton.elim _ _)
      map_comp := fun _ _ => by
        rw [← Subobject.underlying.map_comp]
        exact congrArg _ (Subsingleton.elim _ _) }
  let φ : D ⟶ (Functor.const I).obj M :=
    { app := fun H => (P H).arrow
      naturality := fun {H H'} g => by
        change Subobject.underlying.map (homOfLE (hPle g)) ≫ (P H').arrow = (P H).arrow ≫ 𝟙 M
        rw [Category.comp_id, Subobject.underlying_arrow] }
  refine ⟨I, inferInstance, inferInstance, D, φ, fun H => ?_, ⟨?_⟩⟩
  · exact isCoherent_of_iso B S hS G.objects.2 (e H).symm
      (isCoherent_intersectionPushforward_transitionInclusion objects_noetherian.2.2
        arrows_noetherian.2.2 source_flat source_quasiCompact source_quasiSeparated target_flat M H)
  · exact isColimit_of_iSup_eq_top φ
      (fun H => mono_arrow_hom_of_iso_intersectionPushforward target_flat H.obj.arrow (P H) (e H)
        (he H))
      (iSup_imageSubobject_eq_top_of_iso_intersectionPushforward terminal_mem objects_noetherian
        arrows_noetherian target_flat M P e he)

end QuasicoherentModule

end AlgebraicGeometry.Space

end

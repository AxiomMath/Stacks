module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CommonField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.EtaleLocalizationFiniteSubgroupoid.OrbitFiniteness
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.EtaleLocalizationFiniteSubgroupoid.StableOpenPieces

/-!
# A finite open-and-closed subgroupoid after an étale base change

For a groupoid scheme whose source and target are flat and locally of finite
presentation, a point with finite source fibre and quasi-finite object map has
an elementary étale neighbourhood on which the part of its orbit in the
special fibre extends to a finite open-and-closed subgroupoid.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_subgroupoid`: the finite
  subgroupoid and the complementary open-and-closed pieces after an elementary étale
  base change.

## Implementation notes

The two displayed decompositions in the source are represented by binary
coproduct morphisms which are isomorphisms.  The maps `k` and its two
projection identities say that the composition on the finite groupoid is the
restriction of the original composition.  Thus the bundled groupoid `H`
expresses parts (e)--(g), including the restricted identity and inverse maps.
The two equalities of sets are the set-theoretic fibre assertions (b) and (c),
formed in the *whole* base-changed object and arrow schemes. In particular,
the inverse image in (c) is under the source map on every base-changed arrow,
not only on arrows of the finite subgroupoid.

## References

* [Stacks Project, Tag 03FL](https://stacks.math.columbia.edu/tag/03FL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

attribute [local implicit_reducible] subgroupoidOfCompatibleMaps
attribute [local implicit_reducible] subgroupoidOfCompatibleMapsHom
attribute [local implicit_reducible] subgroupoidOfCompatibleMapsAlong
attribute [local implicit_reducible] subgroupoidOfCompatibleMapsAlongHomOver
attribute [local implicit_reducible] rebaseGroupoid
attribute [local implicit_reducible] rebaseGroupoidProjection
attribute [local implicit_reducible] liftOverOpenImmersion
attribute [local implicit_reducible] groupoidOfStableOpenPieces
attribute [local implicit_reducible] groupoidOfStableOpenPiecesHom
attribute [local implicit_reducible] restrictStablePieces
attribute [local implicit_reducible] restrictStablePiecesHom

private def postcomposeHomOver {S T : Scheme.{u}} {q : T ⟶ S}
    {H : Stacks.Groupoids.GroupoidScheme T} {K G : Stacks.Groupoids.GroupoidScheme S}
    (F : HomOver q H K) (E : Stacks.Groupoids.GroupoidScheme.Hom K G) :
    HomOver q H G := by
  refine
    { mapObjects := F.mapObjects ≫ E.mapObjects
      mapArrows := F.mapArrows ≫ E.mapArrows
      map_source := by simp only [Category.assoc, E.map_source, reassoc_of% F.map_source]
      map_target := by simp only [Category.assoc, E.map_target, reassoc_of% F.map_target]
      map_identity := by simp only [Category.assoc, E.map_identity, reassoc_of% F.map_identity]
      map_comp := ?_ }
  intro Z a b w w'
  have wK : ((Over.map q).map a ≫ F.mapArrows) ≫ K.source =
      ((Over.map q).map b ≫ F.mapArrows) ≫ K.target := by
    simp only [Category.assoc, F.map_source, F.map_target, ← Functor.map_comp_assoc, w]
  rw [← Category.assoc, F.map_comp Z a b w wK]
  exact E.map_comp _ _ _ wK w'

attribute [local implicit_reducible] postcomposeHomOver

private def restrictPieceMap {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B) :
    ((j ≫ f) ⁻¹ᵁ V).toScheme ⟶ B' :=
  h.lift (((j ≫ f) ⁻¹ᵁ V).ι ≫ j) ((j ≫ f) ∣_ V)
    (by rw [Category.assoc, morphismRestrict_ι])

attribute [local implicit_reducible] restrictPieceMap

private lemma restrictPieceMap_fst {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B) :
    restrictPieceMap h j ≫ a = ((j ≫ f) ⁻¹ᵁ V).ι ≫ j := h.lift_fst _ _ _

private lemma restrictPieceMap_snd {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B) :
    restrictPieceMap h j ≫ b = (j ≫ f) ∣_ V := h.lift_snd _ _ _

private lemma restrictPieceMap_isPullback {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B) :
    IsPullback (restrictPieceMap h j) ((j ≫ f) ⁻¹ᵁ V).ι a j := by
  have ho : IsPullback (restrictPieceMap h j ≫ b) ((j ≫ f) ⁻¹ᵁ V).ι V.ι (j ≫ f) := by
    rw [restrictPieceMap_snd]
    exact isPullback_morphismRestrict (j ≫ f) V
  exact ho.of_right (restrictPieceMap_fst h j) h.flip

private lemma restrictPieceMap_range {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B) :
    Set.range (restrictPieceMap h j) = a ⁻¹' Set.range j := by
  have hc := restrictPieceMap_isPullback h j
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.1, ?_⟩
    exact (congrArg (fun f => f y) hc.w).symm
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback hc z y hy.symm
    exact ⟨w, hw⟩

private lemma restrictPieceMap_open_closed {B B' S Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (j : Y ⟶ B)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsOpenImmersion (restrictPieceMap h j) ∧ IsClosedImmersion (restrictPieceMap h j) := by
  have hc := restrictPieceMap_isPullback h j
  rw [← hc.isoPullback_hom_fst]
  constructor <;> infer_instance

private lemma isIso_coprod_desc_restrictPieceMap {B B' S X Y : Scheme.{u}} {V : S.Opens}
    {a : B' ⟶ B} {b : B' ⟶ V.toScheme} {f : B ⟶ S}
    (h : IsPullback a b f V.ι) (i : X ⟶ B) (j : Y ⟶ B)
    [IsOpenImmersion i] [IsClosedImmersion i] [IsOpenImmersion j] [IsClosedImmersion j]
    [IsIso (coprod.desc i j)] :
    IsIso (coprod.desc (restrictPieceMap h i) (restrictPieceMap h j)) := by
  have := (restrictPieceMap_open_closed h i).1
  have := (restrictPieceMap_open_closed h j).1
  have hc : IsCompl (a ⁻¹' Set.range i) (a ⁻¹' Set.range j) :=
    (isCompl_ranges_coprod_desc i j).map (CompleteLatticeHom.setPreimage a)
  have hc' : IsCompl (restrictPieceMap h i).opensRange (restrictPieceMap h j).opensRange := by
    simpa only [isCompl_iff, disjoint_iff, codisjoint_iff,
      ← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_inf,
      TopologicalSpace.Opens.coe_bot, TopologicalSpace.Opens.coe_sup,
      TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_opensRange,
      restrictPieceMap_range, Set.inf_eq_inter, Set.sup_eq_union,
      Set.bot_eq_empty, Set.top_eq_univ] using hc
  obtain ⟨hcolim⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ hc'
  change IsIso ((coprodIsCoprod _ _).coconePointUniqueUpToIso hcolim).hom
  infer_instance

private lemma mem_range_comp_iso_inv {X Y Z : Scheme.{u}} (j : X ⟶ Y) (e : Z ≅ Y)
    (z : Z) : z ∈ Set.range (j ≫ e.inv) ↔ e.hom z ∈ Set.range j := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp only [← Scheme.Hom.comp_apply, Category.assoc, e.inv_hom_id,
      Category.comp_id]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply e.hom.isOpenEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, Category.assoc, e.inv_hom_id,
      Category.comp_id] using hx

private lemma pullback_point_eq_of_residueFieldMap_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z z' : (pullback f g : Scheme))
    (hfst : pullback.fst f g z = pullback.fst f g z')
    (hsnd : pullback.snd f g z = pullback.snd f g z')
    (hiso : IsIso (g.residueFieldMap (pullback.snd f g z'))) : z = z' := by
  let T := Scheme.Pullback.Triplet.ofPoint z'
  have ht : Scheme.Pullback.Triplet.ofPoint z = T :=
    Scheme.Pullback.Triplet.ext hfst hsnd
  let : IsIso (g.residueFieldMap T.y) := hiso
  let : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := by
    infer_instance
  let : IsIso T.tensorInl := by
    change IsIso (pushout.inl
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    infer_instance
  apply Scheme.Pullback.carrierEquiv.injective
  apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
  refine ⟨ht, ?_⟩
  apply (Spec.map T.tensorInl).isOpenEmbedding.injective
  exact Subsingleton.elim _ _

private lemma elementary_residueFieldMap_isIso {S : Scheme.{u}} {p : S}
    (N : AlgebraicGeometry.EtaleNeighborhood S p) (hN : N.IsElementary) :
    IsIso (N.toBase.residueFieldMap N.point) := by
  let : IsIso N.residueFieldMap := hN
  change IsIso ((S.residueFieldCongr N.map_point).inv ≫
    N.toBase.residueFieldMap N.point) at hN
  exact IsIso.of_isIso_comp_left (S.residueFieldCongr N.map_point).inv _

private lemma image_fiber_of_range_iff {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (f : Y ⟶ Z) (p : Z) (A : Set Y)
    (h : ∀ y, f y = p → (y ∈ Set.range j ↔ y ∈ A)) :
    j '' {x | (j ≫ f) x = p} = {y | f y = p ∧ y ∈ A} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, (h _ hx).mp ⟨x, rfl⟩⟩
  · rintro ⟨hy, hA⟩
    obtain ⟨x, rfl⟩ := (h y hy).mpr hA
    exact ⟨x, hy, rfl⟩

/-- A fibre description of `i` transfers along `a` to one for any `j` with range `a ⁻¹' range i`,
when `a` is compatible with the projections to `Q`. -/
private lemma mem_range_iff_of_range_eq_preimage {W X Y Z Q : Scheme.{u}} {i : Z ⟶ Y}
    {j : W ⟶ X} {a : X ⟶ Y} {f : Y ⟶ Q} {f' : X ⟶ Q}
    (hj : Set.range j = a ⁻¹' Set.range i) (hf : a ≫ f = f') {A : Set Q} {z : X}
    (h : a z ∈ Set.range i ↔ f (a z) ∈ A) : z ∈ Set.range j ↔ f' z ∈ A := by
  rw [hj, ← hf, Scheme.Hom.comp_apply]
  exact h

private lemma baseChange_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S)
    (N : AlgebraicGeometry.EtaleNeighborhood S p) (hN : N.IsElementary)
    (u : G.objects.left) (hu : G.objects.hom u = p)
    (v : (pullback G.objects.hom N.toBase : Scheme))
    (hv : pullback.fst G.objects.hom N.toBase v = u)
    (hvp : pullback.snd G.objects.hom N.toBase v = N.point) :
    let s := pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
      G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)
    let t := pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
      G.target.left (𝟙 _) (𝟙 _) (by simp) (by simp)
    t '' (s ⁻¹' {v}) = {z | pullback.snd G.objects.hom N.toBase z = N.point ∧
      pullback.fst G.objects.hom N.toBase z ∈ G.target.left '' (G.source.left ⁻¹' {u})} := by
  intro s t
  have hsf : s ≫ pullback.fst G.objects.hom N.toBase =
      pullback.fst G.arrows.hom N.toBase ≫ G.source.left := by simp [s]
  have htf : t ≫ pullback.fst G.objects.hom N.toBase =
      pullback.fst G.arrows.hom N.toBase ≫ G.target.left := by simp [t]
  have hsb : s ≫ pullback.snd G.objects.hom N.toBase =
      pullback.snd G.arrows.hom N.toBase := by simp [s]
  have htb : t ≫ pullback.snd G.objects.hom N.toBase =
      pullback.snd G.arrows.hom N.toBase := by simp [t]
  have uniq (z z' : (pullback G.objects.hom N.toBase : Scheme))
      (he : pullback.fst G.objects.hom N.toBase z = pullback.fst G.objects.hom N.toBase z')
      (hz : pullback.snd G.objects.hom N.toBase z = N.point)
      (hz' : pullback.snd G.objects.hom N.toBase z' = N.point) : z = z' := by
    apply pullback_point_eq_of_residueFieldMap_isIso _ _ z z' he (hz.trans hz'.symm)
    rw [hz']
    exact elementary_residueFieldMap_isIso N hN
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    change s r = v at hr
    have hsp : pullback.snd G.arrows.hom N.toBase r = N.point := by
      rw [← hsb, Scheme.Hom.comp_apply, hr, hvp]
    refine ⟨?_, pullback.fst G.arrows.hom N.toBase r, ?_, ?_⟩
    · rwa [← Scheme.Hom.comp_apply, htb]
    · change G.source.left (pullback.fst G.arrows.hom N.toBase r) = u
      rw [← Scheme.Hom.comp_apply, ← hsf, Scheme.Hom.comp_apply, hr, hv]
    · exact (congrArg (fun f => f r) htf).symm
  · rintro ⟨hz, r, hrs, hrt⟩
    have hrp : G.arrows.hom r = N.toBase N.point := by
      rw [N.map_point, ← G.source.w, Scheme.Hom.comp_apply, hrs, hu]
    obtain ⟨r', hr'f, hr'b⟩ := Scheme.Pullback.exists_preimage_pullback r N.point hrp
    refine ⟨r', ?_, ?_⟩
    · change s r' = v
      apply uniq _ _ ?_ ?_ hvp
      · rw [← Scheme.Hom.comp_apply, hsf, Scheme.Hom.comp_apply, hr'f, hrs, hv]
      · rw [← Scheme.Hom.comp_apply, hsb, hr'b]
    · apply uniq _ _ ?_ ?_ hz
      · rw [← Scheme.Hom.comp_apply, htf, Scheme.Hom.comp_apply, hr'f, hrt]
      · rw [← Scheme.Hom.comp_apply, htb, hr'b]

private lemma finitePointList_range {α : Type u} (s : Set α) [Fintype s] :
    Set.range (finitePointList s) = s := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact finitePointList_mem s i
  · intro ha
    refine ⟨Fintype.equivFin s ⟨a, ha⟩, ?_⟩
    simp [finitePointList]

attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- Around a point at which the object map is quasi-finite and whose source fibre is finite, a
flat finitely presented groupoid has, after an elementary étale base change, a finite
open-and-closed subgroupoid containing precisely the orbit of the point in the distinguished
fibre. -/
@[stacks 03FL]
public theorem exists_finite_openClosed_subgroupoid
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S)
    (u : G.objects.left) (hu : G.objects.hom u = p)
    [LocallyOfFiniteType G.objects.hom]
    (hqu : AlgebraicGeometry.quasiFiniteAt G.objects.hom u)
    [IsSeparated G.objects.hom] [IsSeparated G.arrows.hom]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    (hfinite : Set.Finite (G.source.left ⁻¹' {u})) :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood S p), N.IsElementary ∧
      ∃ (H : Stacks.Groupoids.GroupoidScheme N.scheme) (W W' : Scheme.{u})
        (jU : H.objects.left ⟶ pullback G.objects.hom N.toBase)
        (jW : W ⟶ pullback G.objects.hom N.toBase)
        (jR : H.arrows.left ⟶ pullback G.arrows.hom N.toBase)
        (jW' : W' ⟶ pullback G.arrows.hom N.toBase),
        IsOpenImmersion jU ∧ IsClosedImmersion jU ∧
        IsOpenImmersion jW ∧ IsClosedImmersion jW ∧
        IsIso (coprod.desc jU jW) ∧
        IsOpenImmersion jR ∧ IsClosedImmersion jR ∧
        IsOpenImmersion jW' ∧ IsClosedImmersion jW' ∧
        IsIso (coprod.desc jR jW') ∧
        H.objects.hom = jU ≫ pullback.snd G.objects.hom N.toBase ∧
        H.arrows.hom = jR ≫ pullback.snd G.arrows.hom N.toBase ∧
        (∃ u' : H.objects.left,
          (jU ≫ pullback.fst G.objects.hom N.toBase) u' = u ∧
          jU '' {x : H.objects.left | H.objects.hom x = N.point} =
            (pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.target.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ''
              ((pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
                G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ⁻¹' {jU u'}) ∧
          jR '' {r : H.arrows.left | H.arrows.hom r = N.point} =
            (pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ⁻¹'
                (jU '' {x : H.objects.left | H.objects.hom x = N.point})) ∧
        IsFinite H.objects.hom ∧ IsFinite H.arrows.hom ∧
        H.source.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
          jR ≫ pullback.fst G.arrows.hom N.toBase ≫ G.source.left ∧
        H.target.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
          jR ≫ pullback.fst G.arrows.hom N.toBase ≫ G.target.left ∧
        ∃ k : (pullback H.source H.target).left ⟶
            (pullback G.source G.target).left,
          k ≫ (pullback.fst G.source G.target).left =
              (pullback.fst H.source H.target).left ≫ jR ≫
                pullback.fst G.arrows.hom N.toBase ∧
          k ≫ (pullback.snd G.source G.target).left =
              (pullback.snd H.source H.target).left ≫ jR ≫
                pullback.fst G.arrows.hom N.toBase ∧
          H.comp.left ≫ jR ≫ pullback.fst G.arrows.hom N.toBase =
            k ≫ G.comp.left := by
  classical
  let orbit := G.target.left '' (G.source.left ⁻¹' {u})
  have orbitFinite : orbit.Finite := source_target_orbit_finite G u hfinite
  let : Fintype orbit := orbitFinite.fintype
  let x : Fin (Fintype.card orbit) → G.objects.left := finitePointList orbit
  have hx : ∀ i, G.objects.hom (x i) = p := fun i =>
    object_point_over_orbit G p u hu (finitePointList_mem orbit i)
  have hxi : Function.Injective x := finitePointList_injective orbit
  have hqfOrbit := quasiFiniteAt_on_source_target_orbit G u hqu hfinite
  have hxiIso : ∀ i, IsOpen {G.objects.hom.asFiber (x i)} := fun i =>
    ((AlgebraicGeometry.quasiFiniteAt_tfae G.objects.hom (x i)).out 1 2).mp
      (hqfOrbit (x i) (finitePointList_mem orbit i))
  obtain ⟨N₁, hN₁, P₁, j₁, hj₁Open, hj₁Closed, hj₁Iso, v₁, hj₁Finite,
      hj₁Point, hj₁Fiber, hj₁Residue, hj₁Complement⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition
      G.objects.hom p (Fintype.card orbit) x hx hxi hxiIso
  let arrowsOrbit := G.source.left ⁻¹' orbit
  have arrowsOrbitFinite : arrowsOrbit.Finite := source_over_orbit_finite G u hfinite
  let : Fintype arrowsOrbit := arrowsOrbitFinite.fintype
  let y : Fin (Fintype.card arrowsOrbit) → G.arrows.left := finitePointList arrowsOrbit
  have hy : ∀ i, G.arrows.hom (y i) = p := fun i =>
    arrow_point_over_source_target_orbit G p u hu (finitePointList_mem arrowsOrbit i)
  have hyi : Function.Injective y := finitePointList_injective arrowsOrbit
  have hyiIso : ∀ i, IsOpen {G.arrows.hom.asFiber (y i)} := fun i =>
    arrows_over_orbit_are_isolated G u hqu hfinite (y i) (finitePointList_mem arrowsOrbit i)
  have : LocallyOfFiniteType G.arrows.hom := by
    rw [← G.source.w]
    infer_instance
  have hyqArrow : ∀ i, AlgebraicGeometry.quasiFiniteAt G.arrows.hom (y i) := by
    intro i
    apply card_quasiFiniteAt_of_quasiFiniteAt
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (hyiIso i)
  obtain ⟨N₂, hN₂, P₂, j₂, hj₂Open, hj₂Closed, hj₂Iso, v₂, hj₂Finite,
      hj₂Point, hj₂Fiber, hj₂Residue, hj₂Complement⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition
      G.arrows.hom p (Fintype.card arrowsOrbit) y hy hyi hyiIso
  have : IsIso (Sigma.desc j₁) := hj₁Iso
  have : IsIso (Sigma.desc j₂) := hj₂Iso
  obtain ⟨U₀, iU₀, hiU₀Open, hiU₀Closed, hiU₀Finite, hiU₀Coprod, hiU₀Range⟩ :=
    finite_union_of_components (pullback.snd G.objects.hom N₁.toBase)
      (Fintype.card orbit) P₁ j₁ hj₁Open hj₁Closed hj₁Finite
  obtain ⟨R₀, iR₀, hiR₀Open, hiR₀Closed, hiR₀Finite, hiR₀Coprod, hiR₀Range⟩ :=
    finite_union_of_components (pullback.snd G.arrows.hom N₂.toBase)
      (Fintype.card arrowsOrbit) P₂ j₂ hj₂Open hj₂Closed hj₂Finite
  have hU₀Fiber (z : (pullback G.objects.hom N₁.toBase : Scheme))
      (hz : pullback.snd G.objects.hom N₁.toBase z = N₁.point) :
      z ∈ Set.range iU₀ ↔ pullback.fst G.objects.hom N₁.toBase z ∈ orbit := by
    rw [hiU₀Range]
    exact (selected_components_fiber _ _ N₁.point P₁ j₁ v₁ x
      hj₁Point hj₁Fiber hj₁Complement z hz).trans
      (by rw [show Set.range x = orbit from finitePointList_range orbit])
  have hR₀Fiber (z : (pullback G.arrows.hom N₂.toBase : Scheme))
      (hz : pullback.snd G.arrows.hom N₂.toBase z = N₂.point) :
      z ∈ Set.range iR₀ ↔ pullback.fst G.arrows.hom N₂.toBase z ∈ arrowsOrbit := by
    rw [hiR₀Range]
    exact (selected_components_fiber _ _ N₂.point P₂ j₂ v₂ y
      hj₂Point hj₂Fiber hj₂Complement z hz).trans
      (by rw [show Set.range y = arrowsOrbit from finitePointList_range arrowsOrbit])
  let common := commonEtaleNeighborhood N₁ N₂ hN₁ hN₂
  let N := common.neighborhood
  let aU := pullbackMapOfEtaleRefinement G.objects.hom N N₁
    common.toFirst common.toFirst_over
  let aR := pullbackMapOfEtaleRefinement G.arrows.hom N N₂
    common.toSecond common.toSecond_over
  have hUcart : IsPullback aU (pullback.snd G.objects.hom N.toBase)
      (pullback.snd G.objects.hom N₁.toBase) common.toFirst :=
    pullback_map_base_isPullback _ _ _ _ common.toFirst_over
  have hRcart : IsPullback aR (pullback.snd G.arrows.hom N.toBase)
      (pullback.snd G.arrows.hom N₂.toBase) common.toSecond :=
    pullback_map_base_isPullback _ _ _ _ common.toSecond_over
  have : IsOpenImmersion iU₀ := hiU₀Open
  have : IsClosedImmersion iU₀ := hiU₀Closed
  have : IsFinite (iU₀ ≫ pullback.snd G.objects.hom N₁.toBase) := hiU₀Finite
  have : IsOpenImmersion iR₀ := hiR₀Open
  have : IsClosedImmersion iR₀ := hiR₀Closed
  have : IsFinite (iR₀ ≫ pullback.snd G.arrows.hom N₂.toBase) := hiR₀Finite
  have : IsIso (coprod.desc iU₀ (j₁ none)) := hiU₀Coprod
  have : IsIso (coprod.desc iR₀ (j₂ none)) := hiR₀Coprod
  have : IsOpenImmersion (j₁ none) := hj₁Open none
  have : IsClosedImmersion (j₁ none) := hj₁Closed none
  have : IsOpenImmersion (j₂ none) := hj₂Open none
  have : IsClosedImmersion (j₂ none) := hj₂Closed none
  let U₁ := pullback iU₀ aU
  let R₁ := pullback iR₀ aR
  let iU₁ : U₁ ⟶ pullback G.objects.hom N.toBase := pullback.snd iU₀ aU
  let iR₁ : R₁ ⟶ pullback G.arrows.hom N.toBase := pullback.snd iR₀ aR
  have hiU₁Finite : IsFinite (iU₁ ≫ pullback.snd G.objects.hom N.toBase) :=
    finite_pullback_piece hUcart iU₀
  have hiR₁Finite : IsFinite (iR₁ ≫ pullback.snd G.arrows.hom N.toBase) :=
    finite_pullback_piece hRcart iR₀
  have hiU₁Coprod : IsIso (coprod.desc iU₁ (pullback.snd (j₁ none) aU)) :=
    isIso_coprod_desc_pullback iU₀ (j₁ none) aU
  have hiR₁Coprod : IsIso (coprod.desc iR₁ (pullback.snd (j₂ none) aR)) :=
    isIso_coprod_desc_pullback iR₀ (j₂ none) aR
  have hU₁Fiber (z : (pullback G.objects.hom N.toBase : Scheme))
      (hz : pullback.snd G.objects.hom N.toBase z = N.point) :
      z ∈ Set.range iU₁ ↔ pullback.fst G.objects.hom N.toBase z ∈ orbit := by
    have hz₀ : pullback.snd G.objects.hom N₁.toBase (aU z) = N₁.point := by
      rw [← Scheme.Hom.comp_apply, hUcart.w, Scheme.Hom.comp_apply, hz]
      exact common.toFirst_point
    exact mem_range_iff_of_range_eq_preimage (IsOpenImmersion.range_pullbackSnd iU₀ aU)
      (pullbackMapOfEtaleRefinement_fst _ _ _ _ _) (hU₀Fiber (aU z) hz₀)
  have hR₁Fiber (z : (pullback G.arrows.hom N.toBase : Scheme))
      (hz : pullback.snd G.arrows.hom N.toBase z = N.point) :
      z ∈ Set.range iR₁ ↔ pullback.fst G.arrows.hom N.toBase z ∈ arrowsOrbit := by
    have hz₀ : pullback.snd G.arrows.hom N₂.toBase (aR z) = N₂.point := by
      rw [← Scheme.Hom.comp_apply, hRcart.w, Scheme.Hom.comp_apply, hz]
      exact common.toSecond_point
    exact mem_range_iff_of_range_eq_preimage (IsOpenImmersion.range_pullbackSnd iR₀ aR)
      (pullbackMapOfEtaleRefinement_fst _ _ _ _ _) (hR₀Fiber (aR z) hz₀)
  have : IsFinite (iU₁ ≫ pullback.snd G.objects.hom N.toBase) := hiU₁Finite
  have : IsFinite (iR₁ ≫ pullback.snd G.arrows.hom N.toBase) := hiR₁Finite
  obtain ⟨BC⟩ := AlgebraicGeometry.GroupoidScheme.exists_baseChange N.toBase G
  let B := BC.groupoid
  let eU := BC.isPullback_objects.isoPullback
  let eR := BC.isPullback_arrows.isoPullback
  let U : Over N.scheme := Over.mk (iU₁ ≫ pullback.snd G.objects.hom N.toBase)
  let R : Over N.scheme := Over.mk (iR₁ ≫ pullback.snd G.arrows.hom N.toBase)
  let jU : U ⟶ B.objects := Over.homMk (iU₁ ≫ eU.inv) (by
    change (iU₁ ≫ eU.inv) ≫ B.objects.hom = _
    rw [Category.assoc, show eU.inv ≫ B.objects.hom =
      pullback.snd G.objects.hom N.toBase from BC.isPullback_objects.isoPullback_inv_snd]
    rfl)
  let jR : R ⟶ B.arrows := Over.homMk (iR₁ ≫ eR.inv) (by
    change (iR₁ ≫ eR.inv) ≫ B.arrows.hom = _
    rw [Category.assoc, show eR.inv ≫ B.arrows.hom =
      pullback.snd G.arrows.hom N.toBase from BC.isPullback_arrows.isoPullback_inv_snd]
    rfl)
  have : IsOpenImmersion jU.left := by
    change IsOpenImmersion (pullback.snd iU₀ aU ≫ eU.inv)
    infer_instance
  have : IsOpenImmersion jR.left := by
    change IsOpenImmersion (pullback.snd iR₀ aR ≫ eR.inv)
    infer_instance
  have : IsFinite U.hom := hiU₁Finite
  have : IsFinite R.hom := hiR₁Finite
  have : IsSeparated B.objects.hom := by
    rw [← BC.isPullback_objects.isoPullback_hom_snd]
    infer_instance
  have hUm (z : B.objects.left) (hz : B.objects.hom z = N.point) :
      z ∈ Set.range jU.left ↔ BC.projection.mapObjects.left z ∈ orbit := by
    have hz' : pullback.snd G.objects.hom N.toBase (eU.hom z) = N.point := by
      rwa [← Scheme.Hom.comp_apply, BC.isPullback_objects.isoPullback_hom_snd]
    exact mem_range_iff_of_range_eq_preimage (Set.ext (mem_range_comp_iso_inv iU₁ eU))
      BC.isPullback_objects.isoPullback_hom_fst (hU₁Fiber (eU.hom z) hz')
  have hRm (z : B.arrows.left) (hz : B.arrows.hom z = N.point) :
      z ∈ Set.range jR.left ↔
        G.source.left (BC.projection.mapArrows.left z) ∈ orbit := by
    have hz' : pullback.snd G.arrows.hom N.toBase (eR.hom z) = N.point := by
      rwa [← Scheme.Hom.comp_apply, BC.isPullback_arrows.isoPullback_hom_snd]
    exact mem_range_iff_of_range_eq_preimage (Set.ext (mem_range_comp_iso_inv iR₁ eR))
      BC.isPullback_arrows.isoPullback_hom_fst (hR₁Fiber (eR.hom z) hz')
  have hBs : B.source.left ≫ BC.projection.mapObjects.left =
      BC.projection.mapArrows.left ≫ G.source.left :=
    (congrArg (fun z => z.left) BC.projection.map_source).symm
  have hBt : B.target.left ≫ BC.projection.mapObjects.left =
      BC.projection.mapArrows.left ≫ G.target.left :=
    (congrArg (fun z => z.left) BC.projection.map_target).symm
  have hsp (r : B.arrows.left) (hr : B.arrows.hom r = N.point) :
      B.objects.hom (B.source.left r) = N.point := by
    simpa only [← Scheme.Hom.comp_apply, B.source.w] using hr
  have htp (r : B.arrows.left) (hr : B.arrows.hom r = N.point) :
      B.objects.hom (B.target.left r) = N.point := by
    simpa only [← Scheme.Hom.comp_apply, B.target.w] using hr
  have hRf (r : B.arrows.left) (hr : B.arrows.hom r = N.point) :
      r ∈ Set.range jR.left ↔ B.source.left r ∈ Set.range jU.left := by
    rw [hRm r hr, hUm _ (hsp r hr)]
    exact Iff.of_eq (congrArg (fun v => v ∈ orbit) (congrArg (fun f => f r) hBs).symm)
  have hstable (r : B.arrows.left) (hr : B.arrows.hom r = N.point)
      (hs : B.source.left r ∈ Set.range jU.left) :
      B.target.left r ∈ Set.range jU.left := by
    rw [hUm _ (hsp r hr)] at hs
    rw [hUm _ (htp r hr)]
    have hs' := congrArg (fun f => f r) hBs
    have ht' := congrArg (fun f => f r) hBt
    change BC.projection.mapObjects.left (B.source.left r) =
      G.source.left (BC.projection.mapArrows.left r) at hs'
    change BC.projection.mapObjects.left (B.target.left r) =
      G.target.left (BC.projection.mapArrows.left r) at ht'
    rw [hs'] at hs
    rw [ht']
    exact target_mem_orbit_of_source_mem G u _ hs
  obtain ⟨V, hpV, hRV, hUV, hCV⟩ :=
    exists_open_stable_pieces B N.point U R jU jR hRf hstable
  let K := restrictStablePieces B U R jU jR V hRV hUV hCV
  let f : K.objects.left ⟶ V.toScheme := U.hom ∣_ V
  have hf : f ≫ V.ι = K.objects.hom := morphismRestrict_ι _ _
  let H := rebaseGroupoid K V.ι f hf
  let M := shrinkEtaleNeighborhood N V hpV
  have hM : M.IsElementary := shrinkEtaleNeighborhood_elementary N common.elementary V hpV
  let F := postcomposeHomOver (rebaseGroupoidProjection K V.ι f hf)
    (restrictStablePiecesHom B U R jU jR V hRV hUV hCV)
  let dU := pullbackMapOfEtaleRefinement G.objects.hom M N V.ι rfl
  let dR := pullbackMapOfEtaleRefinement G.arrows.hom M N V.ι rfl
  have hdU : IsPullback dU (pullback.snd G.objects.hom M.toBase)
      (pullback.snd G.objects.hom N.toBase) V.ι :=
    pullback_map_base_isPullback _ _ _ _ rfl
  have hdR : IsPullback dR (pullback.snd G.arrows.hom M.toBase)
      (pullback.snd G.arrows.hom N.toBase) V.ι :=
    pullback_map_base_isPullback _ _ _ _ rfl
  let J : H.objects.left ⟶ pullback G.objects.hom M.toBase := restrictPieceMap hdU iU₁
  let L : H.arrows.left ⟶ pullback G.arrows.hom M.toBase := restrictPieceMap hdR iR₁
  let gU := pullback.snd (j₁ none) aU
  let gR := pullback.snd (j₂ none) aR
  let JW := restrictPieceMap hdU gU
  let LW := restrictPieceMap hdR gR
  obtain ⟨hJo, hJc⟩ := restrictPieceMap_open_closed hdU iU₁
  obtain ⟨hLo, hLc⟩ := restrictPieceMap_open_closed hdR iR₁
  obtain ⟨hJWo, hJWc⟩ := restrictPieceMap_open_closed hdU gU
  obtain ⟨hLWo, hLWc⟩ := restrictPieceMap_open_closed hdR gR
  have : IsIso (coprod.desc iU₁ gU) := hiU₁Coprod
  have : IsIso (coprod.desc iR₁ gR) := hiR₁Coprod
  have hJU : IsIso (coprod.desc J JW) := isIso_coprod_desc_restrictPieceMap hdU iU₁ gU
  have hLR : IsIso (coprod.desc L LW) := isIso_coprod_desc_restrictPieceMap hdR iR₁ gR
  have hbaseU : H.objects.hom = J ≫ pullback.snd G.objects.hom M.toBase :=
    (restrictPieceMap_snd hdU iU₁).symm
  have hbaseR' : H.arrows.hom = R.hom ∣_ V := by
    apply (cancel_mono V.ι).mp
    change (K.source.left ≫ f) ≫ V.ι = (R.hom ∣_ V) ≫ V.ι
    rw [Category.assoc, hf, K.source.w, morphismRestrict_ι]
    rfl
  have hbaseR : H.arrows.hom = L ≫ pullback.snd G.arrows.hom M.toBase :=
    hbaseR'.trans (restrictPieceMap_snd hdR iR₁).symm
  have hHU : IsFinite H.objects.hom := by change IsFinite (U.hom ∣_ V); infer_instance
  have hHR : IsFinite H.arrows.hom := by rw [hbaseR']; infer_instance
  let qU := F.mapObjects.left ≫ BC.projection.mapObjects.left
  let qR := F.mapArrows.left ≫ BC.projection.mapArrows.left
  have hqU : qU = (U.hom ⁻¹ᵁ V).ι ≫ iU₁ ≫ pullback.fst G.objects.hom N.toBase := by
    change ((𝟙 _) ≫ ((U.hom ⁻¹ᵁ V).ι ≫ (iU₁ ≫ eU.inv))) ≫
      BC.projection.mapObjects.left = _
    simp only [Category.id_comp, Category.assoc]
    rw [show eU.inv ≫ BC.projection.mapObjects.left =
      pullback.fst G.objects.hom N.toBase from BC.isPullback_objects.isoPullback_inv_fst]
  have hqR : qR = (R.hom ⁻¹ᵁ V).ι ≫ iR₁ ≫ pullback.fst G.arrows.hom N.toBase := by
    change ((𝟙 _) ≫ ((R.hom ⁻¹ᵁ V).ι ≫ (iR₁ ≫ eR.inv))) ≫
      BC.projection.mapArrows.left = _
    simp only [Category.id_comp, Category.assoc]
    rw [show eR.inv ≫ BC.projection.mapArrows.left =
      pullback.fst G.arrows.hom N.toBase from BC.isPullback_arrows.isoPullback_inv_fst]
  have hdUf : dU ≫ pullback.fst G.objects.hom N.toBase =
      pullback.fst G.objects.hom M.toBase :=
    pullbackMapOfEtaleRefinement_fst _ _ _ _ _
  have hdRf : dR ≫ pullback.fst G.arrows.hom N.toBase =
      pullback.fst G.arrows.hom M.toBase :=
    pullbackMapOfEtaleRefinement_fst _ _ _ _ _
  have hJfst : J ≫ dU = (U.hom ⁻¹ᵁ V).ι ≫ iU₁ := restrictPieceMap_fst hdU iU₁
  have hLfst : L ≫ dR = (R.hom ⁻¹ᵁ V).ι ≫ iR₁ := restrictPieceMap_fst hdR iR₁
  have hJq : J ≫ pullback.fst G.objects.hom M.toBase = qU := by
    rw [← hdUf, ← Category.assoc, hJfst, hqU, Category.assoc]
  have hLq : L ≫ pullback.fst G.arrows.hom M.toBase = qR := by
    rw [← hdRf, ← Category.assoc, hLfst, hqR, Category.assoc]
  have hsource : H.source.left ≫ qU = qR ≫ G.source.left := by
    have h₁ : F.mapArrows.left ≫ B.source.left = H.source.left ≫ F.mapObjects.left :=
      congrArg (fun z => z.left) F.map_source
    dsimp only [qU, qR]
    rw [← Category.assoc, ← h₁, Category.assoc, hBs, ← Category.assoc]
  have htarget : H.target.left ≫ qU = qR ≫ G.target.left := by
    have h₁ : F.mapArrows.left ≫ B.target.left = H.target.left ≫ F.mapObjects.left :=
      congrArg (fun z => z.left) F.map_target
    dsimp only [qU, qR]
    rw [← Category.assoc, ← h₁, Category.assoc, hBt, ← Category.assoc]
  have hJfiber (z : (pullback G.objects.hom M.toBase : Scheme))
      (hz : pullback.snd G.objects.hom M.toBase z = M.point) :
      z ∈ Set.range J ↔ pullback.fst G.objects.hom M.toBase z ∈ orbit := by
    have hp : pullback.snd G.objects.hom N.toBase (dU z) = N.point := by
      rw [isPullback_w_apply hdU z, hz]
      rfl
    exact mem_range_iff_of_range_eq_preimage (restrictPieceMap_range hdU iU₁) hdUf
      (hU₁Fiber (dU z) hp)
  have hLfiber (z : (pullback G.arrows.hom M.toBase : Scheme))
      (hz : pullback.snd G.arrows.hom M.toBase z = M.point) :
      z ∈ Set.range L ↔ G.source.left (pullback.fst G.arrows.hom M.toBase z) ∈ orbit := by
    have hp : pullback.snd G.arrows.hom N.toBase (dR z) = N.point := by
      rw [isPullback_w_apply hdR z, hz]
      rfl
    exact mem_range_iff_of_range_eq_preimage (restrictPieceMap_range hdR iR₁) hdRf
      (hR₁Fiber (dR z) hp)
  have hJimage : J '' {x : H.objects.left | H.objects.hom x = M.point} =
      {z | pullback.snd G.objects.hom M.toBase z = M.point ∧
        pullback.fst G.objects.hom M.toBase z ∈ orbit} := by
    rw [hbaseU]
    exact image_fiber_of_range_iff J _ M.point _ hJfiber
  have hLimage : L '' {r : H.arrows.left | H.arrows.hom r = M.point} =
      {z | pullback.snd G.arrows.hom M.toBase z = M.point ∧
        G.source.left (pullback.fst G.arrows.hom M.toBase z) ∈ orbit} := by
    rw [hbaseR]
    exact image_fiber_of_range_iff L _ M.point _ hLfiber
  obtain ⟨v, hvf, hvb⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := G.objects.hom) (g := M.toBase) u M.point (hu.trans M.map_point.symm)
  have hvJ : v ∈ Set.range J := (hJfiber v hvb).mpr (by
    rw [hvf]; exact object_lies_in_source_target_orbit G u)
  obtain ⟨u', hu'⟩ := hvJ
  let sM := pullback.map G.arrows.hom M.toBase G.objects.hom M.toBase
    G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  let tM := pullback.map G.arrows.hom M.toBase G.objects.hom M.toBase
    G.target.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hUf : J '' {x : H.objects.left | H.objects.hom x = M.point} =
      tM '' (sM ⁻¹' {J u'}) := by
    rw [hu', hJimage]
    exact (baseChange_orbit G p M hM u hu v hvf hvb).symm
  have hRf' : L '' {r : H.arrows.left | H.arrows.hom r = M.point} =
      sM ⁻¹' (J '' {x : H.objects.left | H.objects.hom x = M.point}) := by
    rw [hLimage, hJimage]
    ext r
    change (pullback.snd G.arrows.hom M.toBase r = M.point ∧
      G.source.left (pullback.fst G.arrows.hom M.toBase r) ∈ orbit) ↔
      (pullback.snd G.objects.hom M.toBase (sM r) = M.point ∧
      pullback.fst G.objects.hom M.toBase (sM r) ∈ orbit)
    have hb : sM ≫ pullback.snd G.objects.hom M.toBase =
        pullback.snd G.arrows.hom M.toBase := by simp [sM]
    have hf' : sM ≫ pullback.fst G.objects.hom M.toBase =
        pullback.fst G.arrows.hom M.toBase ≫ G.source.left := by simp [sM]
    have hb' := congrArg (fun m => m r) hb
    have hf'' := congrArg (fun m => m r) hf'
    change pullback.snd G.objects.hom M.toBase (sM r) = _ at hb'
    change pullback.fst G.objects.hom M.toBase (sM r) = _ at hf''
    rw [hb', hf'']
    rfl
  let T := pullback H.source H.target
  let A := (Over.map V.ι).obj T
  let a : A ⟶ B.arrows := (Over.map V.ι).map (pullback.fst H.source H.target) ≫ F.mapArrows
  let b : A ⟶ B.arrows := (Over.map V.ι).map (pullback.snd H.source H.target) ≫ F.mapArrows
  have wab : a ≫ B.source = b ≫ B.target := by
    simp only [a, b, Category.assoc, F.map_source, F.map_target,
      ← Functor.map_comp_assoc]
    change (Over.map V.ι).map (pullback.fst H.source H.target ≫ H.source) ≫ F.mapObjects =
      (Over.map V.ι).map (pullback.snd H.source H.target ≫ H.target) ≫ F.mapObjects
    rw [pullback.condition]
  let aG := (Over.map N.toBase).map a ≫ BC.projection.mapArrows
  let bG := (Over.map N.toBase).map b ≫ BC.projection.mapArrows
  have wabG : aG ≫ G.source = bG ≫ G.target := by
    simp only [aG, bG, Category.assoc, BC.projection.map_source, BC.projection.map_target,
      ← Functor.map_comp_assoc]
    change (Over.map N.toBase).map (a ≫ B.source) ≫ BC.projection.mapObjects =
      (Over.map N.toBase).map (b ≫ B.target) ≫ BC.projection.mapObjects
    rw [wab]
  let kOver := pullback.lift aG bG wabG
  let k := kOver.left
  have hkf : k ≫ (pullback.fst G.source G.target).left =
      (pullback.fst H.source H.target).left ≫ qR := by
    have hh := congrArg (fun m => m.left) (pullback.lift_fst aG bG wabG)
    simpa only [k, kOver, aG, a, qR, Over.comp_left, Over.map_map_left,
      Category.assoc] using hh
  have hks : k ≫ (pullback.snd G.source G.target).left =
      (pullback.snd H.source H.target).left ≫ qR := by
    have hh := congrArg (fun m => m.left) (pullback.lift_snd aG bG wabG)
    simpa only [k, kOver, bG, b, qR, Over.comp_left, Over.map_map_left,
      Category.assoc] using hh
  have hkc : H.comp.left ≫ qR = k ≫ G.comp.left := by
    have h₁ := F.map_comp T (pullback.fst H.source H.target)
      (pullback.snd H.source H.target) pullback.condition wab
    change (Over.map V.ι).map (H.compose (pullback.fst H.source H.target)
      (pullback.snd H.source H.target) pullback.condition) ≫ F.mapArrows =
      B.compose a b wab at h₁
    simp only [Stacks.Groupoids.GroupoidScheme.compose, pullback.lift_fst_snd,
      Category.id_comp] at h₁
    have h₂ := BC.projection.map_comp A a b wab wabG
    have hh := congrArg (fun m => ((Over.map N.toBase).map m ≫ BC.projection.mapArrows).left) h₁
    have hh₂ := congrArg (fun m => m.left) h₂
    simp only [Stacks.Groupoids.GroupoidScheme.compose,
      Over.comp_left, Over.map_map_left, Category.assoc] at hh hh₂
    exact hh.trans hh₂
  refine ⟨M, hM, H, _, _, J, JW, L, LW, hJo, hJc, hJWo, hJWc, hJU,
    hLo, hLc, hLWo, hLWc, hLR, hbaseU, hbaseR, ?_, hHU, hHR, ?_, ?_,
    k, ?_, ?_, ?_⟩
  · refine ⟨u', ?_, hUf, hRf'⟩
    change pullback.fst G.objects.hom M.toBase (J u') = u
    rw [hu', hvf]
  · simpa only [← hJq, ← hLq, Category.assoc] using hsource
  · simpa only [← hJq, ← hLq, Category.assoc] using htarget
  · rw [hLq]
    exact hkf
  · rw [hLq]
    exact hks
  · rw [hLq]
    exact hkc

end AlgebraicGeometry.GroupoidScheme

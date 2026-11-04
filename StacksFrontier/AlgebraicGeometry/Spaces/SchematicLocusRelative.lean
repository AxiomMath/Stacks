module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability over a test object

Let `π : F ⟶ yoneda.obj T` be a morphism from a sheaf on the big fppf site over `S` to the
functor of points of an object `T` of the site. If the base change of `π` along every member of
an open covering of `T` (for instance, along every affine open of `T`) is represented by an
object of the site whose projection has a property `Q` of scheme morphisms which is Zariski
local at the target, and the glued scheme is contained in the site, then `F` is representable
over `T` with projection having `Q`. This is the relative form of Stacks 03JH. As consequences
we obtain the implications (2) ⇒ (1), (4) ⇒ (1) and (5) ⇒ (1) of Stacks 03WG.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict`: an affine open of an object of
  the site is an object of the site with affine underlying scheme.
* `AlgebraicGeometry.BigFppfSite.contains_of_openCover_affineOpens_of_isRegular`: over a site
  whose cutoff is a regular cardinal, a scheme covered by objects of the site indexed by the
  affine opens of an object of the site is contained in the site.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_openCover`: the base changes of
  `π` along an open covering of the test object cover `F` locally.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isPullback_yoneda_map`: those base changes are
  open immersions of algebraic spaces.
* `AlgebraicGeometry.Space.exists_representing_over_of_openCover`: representability over the
  test object, for an arbitrary open covering of the test object by objects of the site.
* `AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange` and
  `AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange`: the same for the covering by
  the affine opens of the test object, over one test object and over all of them. Their
  `_of_isRegular` variants hold over a site with regular cutoff.
* `AlgebraicGeometry.Space.exists_mem_range_snd_of_zariskiCover` and
  `AlgebraicGeometry.Space.presheaf_of_zariskiCover`: a Zariski covering of the target pulls
  back to a covering of a test object on points, and relative representability with a
  Zariski-local property descends along a Zariski covering of the target.
* `AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom`,
  `AlgebraicGeometry.Space.presheaf_isAffineHom_of_etaleChart_isAffineHom` and
  `AlgebraicGeometry.Space.presheaf_isAffineHom_of_zariskiCover_isAffineHom`: the
  implications (2) ⇒ (1), (4) ⇒ (1) and (5) ⇒ (1) of Stacks 03WG.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine opens of a test object, as objects of the site -/

/-- An affine open of an object of the big fppf category over `S` is again an object of that
category, its inclusion is a morphism of the category which is an open immersion with the
affine open as image, and its underlying scheme is affine. -/
theorem BigFppfOver.exists_affineOpen_restrict (T : BigFppfOver B S hS)
    (U : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    ∃ (V : BigFppfOver B S hS) (u : V ⟶ T),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u) ∧
      Set.range ((BigFppfOver.toScheme B S hS).map u) = (U.1 : Set _) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨V, u, hu, hrange, -⟩ := exists_restrict_bigFppfOver T U.1
  refine ⟨V, u, hu, hrange, ?_⟩
  have h2 : IsAffine (((BigFppfOver.toScheme B S hS).map u).opensRange : Scheme.{u}) := by
    rw [show ((BigFppfOver.toScheme B S hS).map u).opensRange = U.1 from
      TopologicalSpace.Opens.ext hrange]
    exact U.2
  exact IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map u).isoOpensRange.hom

/-- When the cutoff of a big fppf site is a regular cardinal, a scheme covered by the images
of open immersions from objects of the site, indexed by the affine opens of an object `T` of
the site, is itself contained in the site. -/
theorem BigFppfSite.contains_of_openCover_affineOpens_of_isRegular
    (hreg : B.cutoff.IsRegular) (T : BigFppfOver B S hS)
    {W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS}
    (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z)
    (hk : ∀ U, IsOpenImmersion (k U)) (hcov : ∀ z : Z, ∃ U, z ∈ Set.range (k U)) :
    B.Contains Z := by
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T).affineOpens :=
    ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  have hι : Cardinal.mk ((BigFppfOver.toScheme B S hS).obj T).affineOpens <
      B.cutoff.ord.cof :=
    ((BigFppfOver.toScheme B S hS).obj T).mk_affineOpens_le_size.trans_lt
      (lt_of_lt_of_le T.left.property hreg.2)
  exact B.contains_of_openCover hι k hcov fun U => (W U).left.property

namespace Space

/-! ### The charts of a morphism to a test object -/

/-- Let `π : F ⟶ yoneda.obj T` be a morphism of presheaves over an object `T` of the site, and let
`u i : V i ⟶ T` be a family of open immersions of the site whose images cover `T`. If `q i`
presents `yoneda.obj (W i)` as the base change of `π` along `yoneda.map (u i)`, then the `q i`
are jointly locally surjective onto `F` for the fppf topology. -/
theorem isLocallySurjective_sigmaDesc_of_openCover
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : F ⟶ yoneda.obj T}
    {ι : Type u} {V W : ι → BigFppfOver B S hS}
    {u : ∀ i, V i ⟶ T} {p : ∀ i, W i ⟶ V i} {q : ∀ i, yoneda.obj (W i) ⟶ F}
    (hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (u i)))
    (hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u i)))
    (hpb : ∀ i, IsPullback (q i) (yoneda.map (p i)) π (yoneda.map (u i))) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc q) := by
  refine ⟨fun {c} s => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : c ⟶ T, π.app (op c) s = m := ⟨_, rfl⟩
  obtain ⟨σ, hσs⟩ : ∃ σ : yoneda.obj c ⟶ F, yonedaEquiv σ = s :=
    ⟨yonedaEquiv.symm s, Equiv.apply_symm_apply _ _⟩
  have hσπ : σ ≫ π = yoneda.map m :=
    yonedaEquiv.injective (by rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, hσs, hm])
  choose d j hj hjrange _ using fun i : ι => exists_restrict_bigFppfOver c
    ((BigFppfOver.toScheme B S hS).map m ⁻¹ᵁ ((BigFppfOver.toScheme B S hS).map (u i)).opensRange)
  have hjcov : ∀ x : (BigFppfOver.toScheme B S hS).obj c,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    intro x
    obtain ⟨i, hi⟩ := hucov ((BigFppfOver.toScheme B S hS).map m x)
    exact ⟨i, by rw [hjrange i]; exact hi⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j hj hjcov)
  rw [Sieve.generate_le_iff]
  rintro Z z ⟨i⟩
  have hsub : Set.range ((BigFppfOver.toScheme B S hS).map (j i ≫ m)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (u i)) := by
    rintro y ⟨x, rfl⟩
    have hx : (BigFppfOver.toScheme B S hS).map (j i) x ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := ⟨x, rfl⟩
    rw [hjrange i] at hx
    simpa only [Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.coe_preimage,
      Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_opensRange, Set.mem_range] using hx
  obtain ⟨k, hk, -⟩ :=
    BigFppfOver.existsUnique_lift_of_isOpenImmersion (u i) (hu i) (j i ≫ m) hsub
  have hw : (yoneda.map (j i) ≫ σ) ≫ π = yoneda.map k ≫ yoneda.map (u i) := by
    rw [Category.assoc, hσπ, ← Functor.map_comp, ← Functor.map_comp, hk]
  refine ⟨(Sigma.ι (fun i => yoneda.obj (W i)) i).app (op (d i))
    (yonedaEquiv ((hpb i).lift (yoneda.map (j i) ≫ σ) (yoneda.map k) hw)), ?_⟩
  rw [← FunctorToTypes.comp, Sigma.ι_desc, ← yonedaEquiv_comp, (hpb i).lift_fst,
    ← yonedaEquiv_naturality, hσs]

/-- If `q` presents `yoneda.obj W` as the base change of `π : F ⟶ yoneda.obj T` along
`yoneda.map u`, where `u` is an open immersion on underlying schemes, then `q` is an open
immersion of algebraic spaces. -/
theorem isOpenImmersion_of_isPullback_yoneda_map
    {T V W : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : F ⟶ yoneda.obj T}
    {p : W ⟶ V} {u : V ⟶ T} {q : yoneda.obj W ⟶ F}
    (hu : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u))
    (hpb : IsPullback q (yoneda.map p) π (yoneda.map u)) :
    IsOpenImmersion B S hS q := by
  have hst := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ u).2 hu)

/-! ### Relative Tag 03JH -/

/-- Let `π : F ⟶ yoneda.obj T` be a morphism from a sheaf to a representable, and suppose the test
object `T` carries a family of open immersions `u i : V i ⟶ T` covering it along which `π`
becomes representable, by objects `W i` of the site whose projections `p i : W i ⟶ V i` have a
property `Q` of scheme morphisms which is Zariski local at the target. Suppose also
(`hcontains`) that any scheme carrying a jointly surjective family of open immersions from the
`W i` is contained in the site. Then `F` is itself representable over `T`: there is an object
`Y` of the site, an isomorphism `e : F ≅ yoneda.obj Y` and a morphism `P : Y ⟶ T` with
`e.inv ≫ π = yoneda.map P`, and `Q` holds for the underlying morphism of schemes of `P`. -/
@[sga "3 XI 3.4" "special case"]
theorem exists_representing_over_of_openCover
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    {ι : Type u} {V W : ι → BigFppfOver B S hS}
    {u : ∀ i, V i ⟶ T} {p : ∀ i, W i ⟶ V i} {q : ∀ i, yoneda.obj (W i) ⟶ F}
    (hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (u i)))
    (hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u i)))
    (hpb : ∀ i, IsPullback (q i) (yoneda.map (p i)) π (yoneda.map (u i)))
    (hQp : ∀ i, Q ((BigFppfOver.toScheme B S hS).map (p i)))
    (hcontains : ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (W i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  obtain ⟨Y, e, P, g, hP, hfg, -, hgopen, -⟩ :=
    exists_representing_cover_over_of_zariskiCover B S hS hF π W q
      (fun i => isOpenImmersion_of_isPullback_yoneda_map B S hS (hu i) (hpb i))
      (isLocallySurjective_sigmaDesc_of_openCover B S hS hu hucov hpb) hcontains
  refine ⟨Y, e, P, hP, ?_⟩
  have hsq : ∀ i, IsPullback ((BigFppfOver.toScheme B S hS).map (g i))
      ((BigFppfOver.toScheme B S hS).map (p i))
      ((BigFppfOver.toScheme B S hS).map P)
      ((BigFppfOver.toScheme B S hS).map (u i)) :=
    fun i => isPullback_toScheme_of_representing_cover_over B S hS hP (hfg i) (hpb i)
  let 𝒰 : ((BigFppfOver.toScheme B S hS).obj T).OpenCover.{u} :=
    { I₀ := ι
      X := fun i => (BigFppfOver.toScheme B S hS).obj (V i)
      f := fun i => (BigFppfOver.toScheme B S hS).map (u i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hucov, fun i => hu i⟩ }
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun i => ?_
  obtain ⟨w, hwi⟩ : ∃ w : (BigFppfOver.toScheme B S hS).obj (W i) ≅
      Limits.pullback ((BigFppfOver.toScheme B S hS).map P)
        ((BigFppfOver.toScheme B S hS).map (u i)),
      w.hom ≫ Limits.pullback.snd ((BigFppfOver.toScheme B S hS).map P)
        ((BigFppfOver.toScheme B S hS).map (u i)) =
        (BigFppfOver.toScheme B S hS).map (p i) :=
    ⟨(hsq i).isoIsPullback _ _ (IsPullback.of_hasPullback _ _),
      (hsq i).isoIsPullback_hom_snd _ _ _⟩
  exact (Q.cancel_left_of_respectsIso w.hom
    (Limits.pullback.snd ((BigFppfOver.toScheme B S hS).map P)
      ((BigFppfOver.toScheme B S hS).map (u i)))).1 (hwi ▸ hQp i)

/-- If a property `Q` of scheme morphisms which is Zariski local at the target holds on the affine
base changes of `π : F ⟶ yoneda.obj T` in the sense of
`AlgebraicGeometry.Space.HoldsOnAffineBaseChange` — the base change of `π` along every morphism
from an affine object of the site is represented by an affine object whose projection has `Q` —
then `F` is representable over `T` with `Q` holding for the projection, provided (`hcontains`)
every scheme covered by open immersions from affine objects of the site indexed by the affine
opens of `T` is contained in the site. -/
theorem exists_representing_over_of_holdsOnAffineBaseChange
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    (hπ : HoldsOnAffineBaseChange B S hS Q π)
    (hcontains : ∀ (W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens →
        BigFppfOver B S hS),
      (∀ U, IsAffine ((BigFppfOver.toScheme B S hS).obj (W U))) →
      ∀ (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z),
      (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
      (∀ z : Z, ∃ U, z ∈ Set.range (k U)) → B.Contains Z) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  choose V u hu hurange hVaff using
    fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
  choose W p q hpb hWaff hQp using fun U => hπ (V U) (hVaff U) (yoneda.map (u U))
  refine exists_representing_over_of_openCover B S hS hQ hF π
    (V := V) (W := W) (u := u) (p := p) (q := q) hu (fun y => ?_) hpb hQp (hcontains W hWaff)
  have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hy
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨U, by rw [hurange U]; exact hU⟩

/-- Over a site whose cutoff is a regular cardinal: if a property `Q` of scheme morphisms which
is Zariski local at the target holds on the affine base changes of `π : F ⟶ yoneda.obj T`, then
`F` is representable over `T` with `Q` holding for the projection. -/
theorem exists_representing_over_of_holdsOnAffineBaseChange_of_isRegular
    {Q : MorphismProperty Scheme.{u}}
    (hQ : IsZariskiLocalAtTarget Q) (hreg : B.cutoff.IsRegular)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    (hπ : HoldsOnAffineBaseChange B S hS Q π) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) :=
  exists_representing_over_of_holdsOnAffineBaseChange B S hS hQ hF π hπ
    fun _ _ => B.contains_of_openCover_affineOpens_of_isRegular S hS hreg T

/-- If `e` identifies the pullback of `f` along `g` with `W`, and `P : W ⟶ Y` is the transport of
the second projection, then `P` is the second projection of a pullback square with bottom `f` and
`g`. -/
private theorem isPullback_of_iso_pullback {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z} {P : W ⟶ Y} (e : Limits.pullback f g ≅ W)
    (hP : e.inv ≫ Limits.pullback.snd f g = P) :
    IsPullback (e.inv ≫ Limits.pullback.fst f g) P f g :=
  (IsPullback.of_hasPullback f g).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using hP) (by simp) (by simp)

/-- If a property `Q` of scheme morphisms which is Zariski local at the target holds on the affine
base changes of a morphism `π : F ⟶ G` of sheaves, then `π` is relatively representable and
every represented base change of it has `Q`, provided (`hcontains`) that for every object `T`
of the site, every scheme covered by open immersions from affine objects of the site indexed by
the affine opens of `T` is contained in the site. -/
theorem presheaf_of_holdsOnAffineBaseChange
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {π : F ⟶ G}
    (hπ : HoldsOnAffineBaseChange B S hS Q π)
    (hcontains : ∀ (T : BigFppfOver B S hS)
      (W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS),
      (∀ U, IsAffine ((BigFppfOver.toScheme B S hS).obj (W U))) →
      ∀ (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z),
      (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
      (∀ z : Z, ∃ U, z ∈ Set.range (k U)) → B.Contains Z) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf π := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  obtain ⟨Y, e, P, hP, hQP⟩ := exists_representing_over_of_holdsOnAffineBaseChange B S hS
    hQ (BigFppfOver.isSheaf_pullback_yoneda_obj π g hF hG)
    (Limits.pullback.snd π g) (hπ.of_isPullback (IsPullback.of_hasPullback π g)) (hcontains T)
  exact ⟨Y, e.inv ≫ Limits.pullback.fst π g, P, isPullback_of_iso_pullback e hP, hQP⟩

/-- Over a site whose cutoff is a regular cardinal: if a property `Q` of scheme morphisms which
is Zariski local at the target holds on the affine base changes of a morphism `π : F ⟶ G` of
sheaves, then `π` is relatively representable and every represented base change of it has
`Q`. -/
theorem presheaf_of_holdsOnAffineBaseChange_of_isRegular
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    (hreg : B.cutoff.IsRegular) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {π : F ⟶ G}
    (hπ : HoldsOnAffineBaseChange B S hS Q π) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf π :=
  presheaf_of_holdsOnAffineBaseChange B S hS hQ hF hG hπ
    fun T _ _ => B.contains_of_openCover_affineOpens_of_isRegular S hS hreg T


/-- Let `U` be a Zariski covering of a presheaf `Y` on the big fppf category over `S` and let
`h : yoneda.obj T ⟶ Y` be a point of `Y` with values in an object `T` of the site. The members
of the covering are relatively representable, so each pulls back along `h` to an open subobject
`(hU.1 i).2.rep.snd h` of `T`, and those subobjects cover the underlying scheme of `T`. -/
theorem exists_mem_range_snd_of_zariskiCover
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u} {U : I → Subfunctor Y}
    (hU : IsZariskiCover B S hS I U) {T : BigFppfOver B S hS} (h : yoneda.obj T ⟶ Y)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd h)) := by
  have hls := hU.2
  obtain ⟨c, k, ⟨t, ht⟩, z, hz⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
      (Sigma.desc fun i => (U i).ι) (U := op T) (yonedaEquiv h)) y
  obtain ⟨i, hi⟩ := Subfunctor.exists_mem_range_app_of_sigmaDesc (fun i => (U i).ι) (op c) t
  rw [ht] at hi
  obtain ⟨v, hv⟩ := hi
  obtain ⟨l, hl⟩ : ∃ l : yoneda.obj c ⟶ (U i).toFunctor,
      l ≫ (U i).ι = yoneda.map k ≫ h := by
    refine ⟨yonedaEquiv.symm v, ?_⟩
    rw [yonedaEquiv_symm_naturality_right, hv, yonedaEquiv_naturality]
    exact yonedaEquiv.symm_apply_apply _
  obtain ⟨n, hnk⟩ : ∃ n : c ⟶ (hU.1 i).2.rep.pullback h, n ≫ (hU.1 i).2.rep.snd h = k := by
    refine ⟨yoneda.preimage (((hU.1 i).2.rep.isPullback h).lift l (yoneda.map k) hl),
      yoneda.map_injective ?_⟩
    rw [Functor.map_comp, yoneda.map_preimage,
      ((hU.1 i).2.rep.isPullback h).lift_snd l (yoneda.map k) hl]
  refine ⟨i, (BigFppfOver.toScheme B S hS).map n z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hnk]
  exact hz

/-- Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf category over `S`, let `U` be a
Zariski covering of `Y`, and let `Q` be a property of scheme morphisms which is Zariski local
at the target. If the base change of `f` along each member of the covering is relatively
representable with `Q` on its represented base changes, then so is `f`, provided
(`hcontains`) every scheme covered by open immersions from objects of the site indexed by `I`
is contained in the site. -/
@[sga "3 XI 3.4" "special case"]
theorem presheaf_of_zariskiCover
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (hres : ∀ i, (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd f (U i).ι))
    (hcontains : ∀ (W : I → BigFppfOver B S hS) (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (W i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine MorphismProperty.relative.of_exists fun T h => ?_
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ (hU.1 i).2.rep.pullback h)
      (q : yoneda.obj W ⟶ Limits.pullback f h),
      IsPullback q (yoneda.map p) (Limits.pullback.snd f h)
        (yoneda.map ((hU.1 i).2.rep.snd h)) ∧
      Q ((BigFppfOver.toScheme B S hS).map p) := by
    intro i
    have step := ((hres i).rep.isPullback ((hU.1 i).2.rep.fst h)).paste_horiz
      (IsPullback.of_hasPullback f (U i).ι)
    rw [((hU.1 i).2.rep.isPullback h).w] at step
    exact ⟨_, _, _, IsPullback.of_right' step (IsPullback.of_hasPullback f h),
      (hres i).property_snd _⟩
  choose W p q hpb hQp using key
  obtain ⟨Y', e, P, hP, hQP⟩ := exists_representing_over_of_openCover B S hS hQ
    (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY) (Limits.pullback.snd f h)
    (V := fun i => (hU.1 i).2.rep.pullback h) (W := W)
    (u := fun i => (hU.1 i).2.rep.snd h) (p := p) (q := q)
    (fun i => (hU.1 i).2.property_snd h)
    (exists_mem_range_snd_of_zariskiCover B S hS hU h) hpb hQp (hcontains W)
  exact ⟨Y', e.inv ≫ Limits.pullback.fst f h, P, isPullback_of_iso_pullback e hP, hQP⟩

/-- Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf category over `S`, let `U` be a
Zariski covering of `Y` indexed by a nonempty type of cardinality below the cofinality of the
cutoff of the site, and let `Q` be a property of scheme morphisms which is Zariski local at the
target. If the base change of `f` along each member of the covering is relatively
representable with `Q` on its represented base changes, then so is `f`. -/
theorem presheaf_of_zariskiCover_of_lt_cof
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {I : Type u} [Nonempty I] (hI : Cardinal.mk I < B.cutoff.ord.cof)
    {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (hres : ∀ i, (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd f (U i).ι)) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_of_zariskiCover B S hS hQ hX hY hU hres fun W _ k _ hcov =>
    B.contains_of_openCover hI k hcov fun i => (W i).left.property


/-! ### Stacks 03WG -/

/-- An affine morphism of algebraic spaces over `S` in the sense of Stacks 03WF is representable,
and all of its represented base changes are affine morphisms of schemes, provided the
containment hypothesis `hcontains` holds. This is the implication (2) ⇒ (1) of Stacks 03WG. -/
theorem presheaf_isAffineHom_of_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    (hf : IsAffineHom B S hS f)
    (hcontains : ∀ (T : BigFppfOver B S hS)
      (W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS),
      (∀ U, IsAffine ((BigFppfOver.toScheme B S hS).obj (W U))) →
      ∀ (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z),
      (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
      (∀ z : Z, ∃ U, z ∈ Set.range (k U)) → B.Contains Z) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have h := presheaf_of_holdsOnAffineBaseChange B S hS
    isZariskiLocalAtTarget_isAffineHom hX hY
    ((isAffineHom_iff_holdsOnAffineBaseChange f).1 hf) hcontains
  exact ⟨h.rep, h⟩

/-- Assume effective descent of affine morphisms along surjective étale morphisms (`hdesc`,
Stacks 03I2) and the containment hypothesis `hcontains`. If some surjective étale chart `g` of
the target makes the base change of `f` along it an affine morphism of algebraic spaces, then
`f` is representable with affine represented base changes. This is the implication
(4) ⇒ (1) of Stacks 03WG. -/
theorem presheaf_isAffineHom_of_etaleChart_isAffineHom
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : IsSurjective B S hS g) (he : IsEtale B S hS g)
    (h₄ : IsAffineHom B S hS (Limits.pullback.snd f g))
    (hcontains : ∀ (T : BigFppfOver B S hS)
      (W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS),
      (∀ U, IsAffine ((BigFppfOver.toScheme B S hS).obj (W U))) →
      ∀ (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z),
      (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
      (∀ z : Z, ∃ U, z ∈ Set.range (k U)) → B.Contains Z) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_isAffineHom_of_surjectiveEtaleChart hdesc hX hY hs he
    (presheaf_of_holdsOnAffineBaseChange B S hS isZariskiLocalAtTarget_isAffineHom
      (BigFppfOver.isSheaf_pullback_yoneda_obj f g hX.isSheaf hY.isSheaf)
      (BigFppfOver.isSheaf_yoneda_obj B S hS V)
      ((isAffineHom_iff_holdsOnAffineBaseChange _).1 h₄) hcontains)

/-- If `f` is an affine morphism of algebraic spaces over the members of some Zariski covering of
its target, then `f` is representable with affine represented base changes, provided the
containment hypotheses `hcontains` (indexed by the affine opens of a test object) and
`hcontainsCover` (indexed by the index type of the covering) hold. This is the implication
(5) ⇒ (1) of Stacks 03WG. -/
theorem presheaf_isAffineHom_of_zariskiCover_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h₅ : ∀ i, IsAffineHom B S hS (Limits.pullback.snd f (U i).ι))
    (hcontains : ∀ (T : BigFppfOver B S hS)
      (W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS),
      (∀ U, IsAffine ((BigFppfOver.toScheme B S hS).obj (W U))) →
      ∀ (Z : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Z),
      (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
      (∀ z : Z, ∃ U, z ∈ Set.range (k U)) → B.Contains Z)
    (hcontainsCover : ∀ (W : I → BigFppfOver B S hS) (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (W i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have h := presheaf_of_zariskiCover B S hS isZariskiLocalAtTarget_isAffineHom
    hX.isSheaf hY.isSheaf hU
    (fun i => presheaf_of_holdsOnAffineBaseChange B S hS
      isZariskiLocalAtTarget_isAffineHom
      (Presheaf.isSheaf_pullback _ f (U i).ι hX.isSheaf (hU.1 i).1.isSheaf hY.isSheaf)
      (hU.1 i).1.isSheaf ((isAffineHom_iff_holdsOnAffineBaseChange _).1 (h₅ i)) hcontains)
    hcontainsCover
  exact ⟨h.rep, h⟩

end Space

end AlgebraicGeometry

end

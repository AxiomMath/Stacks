module

public import StacksFrontier.AlgebraicGeometry.Fibres.ClopenFibreEtaleExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The fibres of a proper morphism to a scheme whose clopen sets descend are connected

Let `g : X ⟶ h_W` be a proper morphism from an algebraic space to the presheaf represented by a
scheme `W` of the site, and suppose that for every étale morphism `T ⟶ W` from a scheme of the
site, every open and closed set of points of `X ×_W T` is the preimage of a set of points of
`T`.  Then for every point `w ∈ W` the set-theoretic fibre `{x ∈ |X| : g(x) = w}` is
preconnected (`AlgebraicGeometry.Space.isPreconnected_fibre_of_forall_isClopen_eq_preimage`).

This is the heart of the connectedness clause of the Stein factorization of a proper morphism
of algebraic spaces, Stacks 0A1C: for the first factor `f' : X ⟶ Y'` of the Stein factorization,
`f'_*𝒪_X = 𝒪_{Y'}`, and that is exactly what makes clopen sets of points descend
(`AlgebraicGeometry.Space.exists_eq_preimage_of_isClopen_of_isIso_fSharp`).

## Implementation notes

The source proves the connectedness by absolute Noetherian approximation of the proper
algebraic space (Stacks 0A0X) and the Noetherian case through the theorem on formal functions
for algebraic spaces (Stacks 0A1B, 08B1).  Neither is available here for algebraic spaces, and
the argument below replaces them by Chow's lemma for algebraic spaces and the scheme case.

Suppose the fibre `Z` over `w` is split by two disjoint opens `u` and `v` of `|X|`.  Over an
affine open `W' ∋ w` Chow's lemma (Stacks 089J) gives a proper surjective `p : X'' ⟶ X_{W'}`
with `X''` a scheme, proper over `W'`.  The trace `C` of `u` on the scheme fibre `X''_{w}` is
open and closed.  For a proper morphism of schemes such a set extends, after an étale base change
`T' ⟶ W'` at a point `v'` over `w`, to an open and closed subset `A` of `X''_{T'}`
(`AlgebraicGeometry.exists_etale_isClopen_extension_of_isProper`, which rests on Stacks 0G7X and
00UK).  The images of `A` and of its complement under the proper surjective
`p_{T'} : X''_{T'} ⟶ X_{T'}` are closed and cover `|X_{T'}|`; they meet in a closed set not
lying over `v'`, because over `v'` membership in `A` is membership in `u` of the image in `X`.
Removing the image of that closed set from `T'` leaves an étale neighbourhood `T₂` of `v'` over
which the two images form a clopen partition of `|X_{T₂}|` with points over `v'` on both sides —
the images of the points of `Z ∩ u` and of `Z ∩ v`.  By hypothesis the partition descends to
`T₂`, which is absurd at `v'`.

## References

* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The object of the big fppf site of `S` given by a scheme `Y` of the site with a morphism
`m : Y ⟶ W` to the scheme underlying an object `W`, structured over `S` through `W`. -/
noncomputable def siteObjectOver (W : BigFppfOver B S hS) {Y : Scheme.{u}} (hY : B.Contains Y)
    (m : Y ⟶ (BigFppfOver.toScheme B S hS).obj W) : BigFppfOver B S hS :=
  Over.mk ((⟨m⟩ : B.obj hY ⟶ W.left) ≫ W.hom)

/-- The morphism of the big fppf site from `AlgebraicGeometry.Space.siteObjectOver` to `W`. -/
noncomputable def siteObjectOverHom (W : BigFppfOver B S hS) {Y : Scheme.{u}}
    (hY : B.Contains Y) (m : Y ⟶ (BigFppfOver.toScheme B S hS).obj W) :
    siteObjectOver W hY m ⟶ W :=
  Over.homMk ⟨m⟩ rfl

/-- `AlgebraicGeometry.exists_etale_isClopen_extension_of_isProper` for an arbitrary cartesian
square over the étale base change rather than the chosen fibre product. -/
theorem _root_.AlgebraicGeometry.exists_etale_isClopen_extension_of_isProper_of_isPullback
    {X T : Scheme.{u}} (ψ : X ⟶ T) [_root_.AlgebraicGeometry.IsProper ψ] (v : T)
    (C : (ψ.fiber v).Opens) (hC : IsClosed (C : Set (ψ.fiber v))) :
    ∃ (R' : CommRingCat.{u}) (τ : Spec R' ⟶ T) (_ : Etale τ) (v' : Spec R'), τ v' = v ∧
      ∀ {P : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Spec R'), IsPullback fst snd ψ τ →
        ∃ A : P.Opens, IsClosed (A : Set P) ∧ ∀ z : P, snd z = v' →
          (z ∈ A ↔ ∃ c ∈ C, ψ.fiberι v c = fst z) := by
  obtain ⟨R', τ, hτ, v', hτv, A, hAcl, hA⟩ :=
    exists_etale_isClopen_extension_of_isProper ψ v C hC
  refine ⟨R', τ, hτ, v', hτv, fun {P} fst snd h => ?_⟩
  refine ⟨h.isoPullback.hom ⁻¹ᵁ A, hAcl.preimage h.isoPullback.hom.continuous, fun z hz => ?_⟩
  have hs : Limits.pullback.snd ψ τ (h.isoPullback.hom z) = v' := by
    rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_snd]
  have hf : Limits.pullback.fst ψ τ (h.isoPullback.hom z) = fst z := by
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst]
  rw [← hf]
  exact hA _ hs

/-- A continuous map into a space covered by two open sets which no point of the image lies in
both pulls the first back to a clopen set. -/
theorem _root_.isClopen_preimage_of_forall_mem_iff_notMem {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Continuous f) {U V : Set β} (hU : IsOpen U)
    (hV : IsOpen V) (h : ∀ a, f a ∈ U ↔ f a ∉ V) : IsClopen (f ⁻¹' U) :=
  ⟨by rw [show f ⁻¹' U = (f ⁻¹' V)ᶜ from Set.ext h]; exact (hV.preimage hf).isClosed_compl,
    hU.preimage hf⟩

/-- If `p` is a closed surjection and `A` is clopen, the preimage under a continuous `m` of
`p '' A` is clopen as soon as no point of the image of `m` lies in both `p '' A` and
`p '' Aᶜ`. -/
theorem _root_.isClopen_preimage_image_of_surjective {P Y Z : Type*} [TopologicalSpace P]
    [TopologicalSpace Y] [TopologicalSpace Z] {p : P → Y} {m : Z → Y}
    (hpS : Function.Surjective p) (hpc : IsClosedMap p) (hm : Continuous m) {A : Set P}
    (hA : IsClopen A) (h : ∀ z, m z ∈ p '' A → m z ∉ p '' Aᶜ) :
    IsClopen (m ⁻¹' (p '' A)) := by
  refine ⟨(hpc _ hA.isClosed).preimage hm, ?_⟩
  have : m ⁻¹' (p '' A) = (m ⁻¹' (p '' Aᶜ))ᶜ := by
    refine Set.ext fun z => ⟨h z, fun hz => ?_⟩
    obtain ⟨a, ha⟩ := hpS (m z)
    by_contra hz'
    exact hz ⟨a, fun haA => hz' ⟨a, haA, ha⟩, ha⟩
  rw [this]
  exact ((hpc _ hA.isOpen.isClosed_compl).preimage hm).isOpen_compl

/-- Given a cartesian square `sq` and a cartesian square over `ψ = p ≫ g₂` and `τ`, the induced
morphism to the corner of `sq` is a base change of `p`. -/
theorem _root_.CategoryTheory.IsPullback.exists_isPullback_of_comp {C : Type*} [Category C]
    {P Q X₁ X₂ Y₁ Y₂ : C} {m : X₁ ⟶ X₂} {g₁ : X₁ ⟶ Y₁} {g₂ : X₂ ⟶ Y₂} {τ : Y₁ ⟶ Y₂}
    (sq : IsPullback m g₁ g₂ τ) {p : Q ⟶ X₂} {ψ : Q ⟶ Y₂} (hψ : p ≫ g₂ = ψ)
    {fst : P ⟶ Q} {snd : P ⟶ Y₁} (h : IsPullback fst snd ψ τ) :
    ∃ p₁ : P ⟶ X₁, p₁ ≫ m = fst ≫ p ∧ p₁ ≫ g₁ = snd ∧ IsPullback p₁ fst m p := by
  refine ⟨sq.lift (fst ≫ p) snd (by rw [Category.assoc, hψ, h.w]), sq.lift_fst _ _ _,
    sq.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (sq.lift_fst _ _ _) sq.flip
  rw [sq.lift_snd, hψ]
  exact h.flip

/-- In a cartesian square of schemes, a point `z` over `t` lies over a point `c` of the fibre of
`ψ` over `w = τ t`; any description of a set of such `z` by fibre points is evaluated at `c`. -/
theorem _root_.AlgebraicGeometry.exists_fiberι_eq_of_isPullback {P X T W : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ T} {ψ : X ⟶ W} {τ : T ⟶ W} (sq : IsPullback fst snd ψ τ)
    {w : W} {t : T} (ht : τ t = w) {R : P → Prop} {Q : ψ.fiber w → Prop}
    (hR : ∀ z, snd z = t → (R z ↔ ∃ c, Q c ∧ ψ.fiberι w c = fst z)) {z : P}
    (hz : snd z = t) : ∃ c, ψ.fiberι w c = fst z ∧ (R z ↔ Q c) := by
  obtain ⟨c, hc⟩ : fst z ∈ Set.range (ψ.fiberι w) := by
    rw [Scheme.Hom.range_fiberι]
    change ψ (fst z) = w
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply, hz, ht]
  refine ⟨c, hc, (hR z hz).trans ⟨?_, fun h => ⟨c, h, hc⟩⟩⟩
  rintro ⟨c', hc', hc'z⟩
  rwa [← (ψ.fiberι w).isEmbedding.injective (hc'z.trans hc.symm)]

/-- An affine scheme locally of finite type over a scheme of the site is a scheme of the site. -/
theorem contains_spec_of_locallyOfFiniteType {Y : Scheme.{u}} (hY : B.Contains Y)
    {R : CommRingCat.{u}} (f : Spec R ⟶ Y) [LocallyOfFiniteType f] : B.Contains (Spec R) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit f (fun _ : PUnit => ⟨⊤, isAffineOpen_top (Spec R)⟩) (by simp)
    ((Cardinal.mk_le_aleph0.trans (Scheme.aleph0_le_size _)).trans
      (Cardinal.self_le_power _ Cardinal.one_le_aleph0)) hY

/-- A point of `X` whose image in `h_U` is the image of a scheme point `t` of `T` lifts to the
fibre product `X ×_{h_U} h_T`, with image `t` in `T`. -/
theorem exists_points_of_isPullback_yoneda_map {P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T U : BigFppfOver B S hS} {fst : P ⟶ X} {snd : P ⟶ yoneda.obj T} {f : X ⟶ yoneda.obj U}
    {τ : T ⟶ U} (sq : IsPullback fst snd f (yoneda.map τ)) (x : points B S hS X)
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (hx : pointsToScheme B S hS U (pointsMap B S hS X f x) =
      (BigFppfOver.toScheme B S hS).map τ t) :
    ∃ x' : points B S hS P, pointsMap B S hS P fst x' = x ∧
      pointsToScheme B S hS T (pointsMap B S hS P snd x') = t := by
  have hab : pointsMap B S hS X f x =
      pointsMap B S hS _ (yoneda.map τ) ((schemePointsHomeomorph B S hS T).symm t) := by
    apply injective_pointsToScheme B S hS U
    rw [hx, pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply,
      Homeomorph.apply_symm_apply]
  obtain ⟨x', h₁, h₂⟩ := exists_points_of_isPullback B S hS sq x _ hab
  refine ⟨x', h₁, ?_⟩
  rw [h₂, ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The composite of two morphisms of the site which are étale on underlying schemes is étale. -/
private theorem etale_map_comp {T U W : BigFppfOver B S hS} {κ : T ⟶ U} {τ : U ⟶ W}
    (hκ : Etale ((BigFppfOver.toScheme B S hS).map κ))
    (hτ : Etale ((BigFppfOver.toScheme B S hS).map τ)) :
    Etale ((BigFppfOver.toScheme B S hS).map (κ ≫ τ)) := by
  rw [Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ hκ hτ

/-- **Descent of a clopen partition.**  Let `X₁ = X ×_W T` for an étale `τ : T ⟶ W`, and let
`p : P ⟶ X₁` be surjective and closed on points, with `X₁ ⟶ h_T` closed on points.  If clopen
sets of points descend along étale base change of `X ⟶ h_W`, then a clopen set `A` of points of
`P` which is a union of fibres of `p` over a point `t` of `T` contains every point over `t` as
soon as it contains one. -/
theorem mem_of_mem_of_forall_isClopen_eq_preimage
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS} {g : X ⟶ yoneda.obj W}
    (hdesc : ∀ (T : BigFppfOver B S hS) (τ : T ⟶ W),
      Etale ((BigFppfOver.toScheme B S hS).map τ) →
      ∀ A : Set (points B S hS (pullback g (yoneda.map τ))), IsClopen A →
        ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x, x ∈ A ↔
          pointsToScheme B S hS T (pointsMap B S hS _ (pullback.snd g (yoneda.map τ)) x) ∈ D)
    {T : BigFppfOver B S hS} {τ : T ⟶ W} (hτ : Etale ((BigFppfOver.toScheme B S hS).map τ))
    {X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ξ : X₁ ⟶ X} {g₁ : X₁ ⟶ yoneda.obj T}
    (sq : IsPullback ξ g₁ g (yoneda.map τ)) (hg₁ : IsClosedMap (pointsMap B S hS X₁ g₁))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ X₁}
    (hpS : Function.Surjective (pointsMap B S hS P p)) (hpc : IsClosedMap (pointsMap B S hS P p))
    {A : Set (points B S hS P)} (hA : IsClopen A) {t : (BigFppfOver.toScheme B S hS).obj T}
    (hAt : ∀ a b, pointsToScheme B S hS T (pointsMap B S hS X₁ g₁ (pointsMap B S hS P p a)) = t →
      pointsMap B S hS P p a = pointsMap B S hS P p b → a ∈ A → b ∈ A)
    {a b : points B S hS P} (ha : a ∈ A)
    (hat : pointsToScheme B S hS T (pointsMap B S hS X₁ g₁ (pointsMap B S hS P p a)) = t)
    (hbt : pointsToScheme B S hS T (pointsMap B S hS X₁ g₁ (pointsMap B S hS P p b)) = t) :
    b ∈ A := by
  by_contra hb
  set K := pointsMap B S hS P p '' A ∩ pointsMap B S hS P p '' Aᶜ
  have hK : ∀ y ∈ K, pointsToScheme B S hS T (pointsMap B S hS X₁ g₁ y) ≠ t := by
    rintro y ⟨⟨a', ha', rfl⟩, ⟨b', hb', hab⟩⟩ hy
    exact hb' (hAt a' b' hy hab.symm ha')
  set L := pointsToScheme B S hS T '' (pointsMap B S hS X₁ g₁ '' K)
  have hLcl : IsClosed L := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS T _).mp
    (hg₁ _ ((hpc _ hA.isClosed).inter (hpc _ hA.isOpen.isClosed_compl)))
  have htL : t ∉ L := by
    rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    exact hK y hy h
  set O : ((BigFppfOver.toScheme B S hS).obj T).Opens := ⟨Lᶜ, hLcl.isOpen_compl⟩
  have hO : B.Contains O.toScheme := Scheme.size_lt_of_isOpenImmersion O.ι T.left.property
  set κ := siteObjectOverHom T hO O.ι
  obtain ⟨m, hm, -, sqm⟩ := sq.flip.exists_isPullback_of_comp (yoneda.map_comp κ τ).symm
    (IsPullback.of_hasPullback g (yoneda.map (κ ≫ τ))).flip
  have hdisj : ∀ x, pointsMap B S hS _ m x ∈ pointsMap B S hS P p '' A →
      pointsMap B S hS _ m x ∉ pointsMap B S hS P p '' Aᶜ := by
    intro x hxA hxB
    have hmem : pointsToScheme B S hS T (pointsMap B S hS X₁ g₁ (pointsMap B S hS _ m x)) ∈
        (O : Set _) := by
      rw [← pointsMap_comp_apply, hm, pointsMap_comp_apply, pointsToScheme_pointsMap_yoneda]
      exact (Scheme.Opens.range_ι O).le ⟨_, rfl⟩
    exact hmem ⟨_, ⟨_, ⟨hxA, hxB⟩, rfl⟩, rfl⟩
  obtain ⟨D, hD⟩ := hdesc _ (κ ≫ τ) (etale_map_comp (inferInstance : Etale O.ι) hτ) _
    (isClopen_preimage_image_of_surjective hpS hpc (continuous_pointsMap B S hS m) hA hdisj)
  obtain ⟨x, hxm, hx⟩ := exists_points_of_isPullback_yoneda_map sqm _ (⟨t, htL⟩ : O.toScheme) hat
  obtain ⟨y, hym, hy⟩ := exists_points_of_isPullback_yoneda_map sqm _ (⟨t, htL⟩ : O.toScheme) hbt
  have h := (hD x).1 ⟨a, ha, hxm.symm⟩
  rw [hx] at h
  exact hdisj y ((hD y).2 (hy ▸ h)) ⟨b, hb, hym.symm⟩

/-- **The étale step over a Chow cover.**  Let `X' = X ×_W W'` for an étale `j : W' ⟶ W`, and
let `p : h_{X''} ⟶ X'` be universally closed and surjective with `p ≫ (X' ⟶ h_{W'})` given by a
proper morphism of schemes `ψ : X'' ⟶ W'`.  If clopen sets of points descend along étale base
change of `X ⟶ h_W`, then a set `U` of points of `X'` whose trace on the scheme fibre of `ψ` over
`w'` is clopen contains every point of `X'` over `w'` as soon as it contains one. -/
theorem mem_of_mem_of_isClopen_preimage_fiberι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} {g : X ⟶ yoneda.obj W} (hg : IsProper B S hS g)
    (hdesc : ∀ (T : BigFppfOver B S hS) (τ : T ⟶ W),
      Etale ((BigFppfOver.toScheme B S hS).map τ) →
      ∀ A : Set (points B S hS (pullback g (yoneda.map τ))), IsClopen A →
        ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x, x ∈ A ↔
          pointsToScheme B S hS T (pointsMap B S hS _ (pullback.snd g (yoneda.map τ)) x) ∈ D)
    {W' : BigFppfOver B S hS} (j : W' ⟶ W) (hj : Etale ((BigFppfOver.toScheme B S hS).map j))
    {X'' : BigFppfOver B S hS} (ψ : X'' ⟶ W')
    (hψ : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ψ))
    (p : yoneda.obj X'' ⟶ pullback g (yoneda.map j))
    (hpψ : p ≫ pullback.snd g (yoneda.map j) = yoneda.map ψ)
    (hpS : Function.Surjective (pointsMap B S hS _ p)) (hpC : UniversallyClosed B S hS p)
    (w' : (BigFppfOver.toScheme B S hS).obj W')
    {U : Set (points B S hS (pullback g (yoneda.map j)))}
    (hU : IsClopen ((fun c : ((BigFppfOver.toScheme B S hS).map ψ).fiber w' =>
      pointsMap B S hS _ p ((schemePointsHomeomorph B S hS X'').symm
        (((BigFppfOver.toScheme B S hS).map ψ).fiberι w' c))) ⁻¹' U))
    {x y : points B S hS (pullback g (yoneda.map j))}
    (hx : pointsToScheme B S hS W' (pointsMap B S hS _ (pullback.snd g (yoneda.map j)) x) = w')
    (hy : pointsToScheme B S hS W' (pointsMap B S hS _ (pullback.snd g (yoneda.map j)) y) = w')
    (hxU : x ∈ U) : y ∈ U := by
  have hYW := isAlgebraicSpace_yoneda B S hS W
  have hX' := isAlgebraicSpace_pullback B S hS g (yoneda.map j) hX
    (isAlgebraicSpace_yoneda B S hS W') hYW
  obtain ⟨R', τs, hτs, v', hτv, hext⟩ :=
    exists_etale_isClopen_extension_of_isProper_of_isPullback _ w' ⟨_, hU.isOpen⟩ hU.isClosed
  have hT' : B.Contains (Spec R') := contains_spec_of_locallyOfFiniteType W'.left.property τs
  set τ := siteObjectOverHom W' hT' τs
  have hYT' := isAlgebraicSpace_yoneda B S hS (siteObjectOver W' hT' τs)
  have hX₁ := isAlgebraicSpace_pullback B S hS g (yoneda.map (τ ≫ j)) hX hYT' hYW
  have sqX₁ := IsPullback.of_hasPullback g (yoneda.map (τ ≫ j))
  have hg₁ := isProper_of_isPullback B S hS hX₁ hX hYT' hYW sqX₁ hg
  obtain ⟨m, -, -, sqm⟩ :=
    (IsPullback.of_hasPullback g (yoneda.map j)).flip.exists_isPullback_of_comp
      (yoneda.map_comp τ j).symm sqX₁.flip
  have sqP := IsPullback.of_hasPullback ψ τ
  obtain ⟨p₁, hp₁m, hp₁g, sqp₁⟩ := sqm.exists_isPullback_of_comp hpψ (sqP.map yoneda)
  obtain ⟨A, hAcl, hA⟩ := hext _ _ (sqP.map (BigFppfOver.toScheme B S hS))
  have hkey : ∀ a, pointsToScheme B S hS _
      (pointsMap B S hS _ (yoneda.map (Limits.pullback.snd ψ τ)) a) = v' →
      (pointsToScheme B S hS _ a ∈ A ↔ pointsMap B S hS _ m (pointsMap B S hS _ p₁ a) ∈ U) := by
    intro a ha
    obtain ⟨c, hc, hcA⟩ := exists_fiberι_eq_of_isPullback (sqP.map (BigFppfOver.toScheme B S hS))
      (t := v') (w := w') hτv hA
      ((pointsToScheme_pointsMap_yoneda B S hS (Limits.pullback.snd ψ τ) a).symm.trans ha)
    have hq : (schemePointsHomeomorph B S hS X'').symm
        (((BigFppfOver.toScheme B S hS).map ψ).fiberι w' c) =
          pointsMap B S hS _ (yoneda.map (Limits.pullback.fst ψ τ)) a := by
      apply (schemePointsHomeomorph B S hS X'').injective
      rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
        pointsToScheme_pointsMap_yoneda, hc]
    rw [hcA, ← pointsMap_comp_apply, hp₁m, pointsMap_comp_apply, ← hq]
    exact Iff.rfl
  have hover : ∀ a, pointsToScheme B S hS _ (pointsMap B S hS _
      (pullback.snd g (yoneda.map (τ ≫ j))) (pointsMap B S hS _ p₁ a)) = pointsToScheme B S hS _
        (pointsMap B S hS _ (yoneda.map (Limits.pullback.snd ψ τ)) a) := fun a => by
    rw [← pointsMap_comp_apply, hp₁g]
  have hlift : ∀ z, pointsToScheme B S hS W'
      (pointsMap B S hS _ (pullback.snd g (yoneda.map j)) z) = w' →
      ∃ a, pointsToScheme B S hS _
        (pointsMap B S hS _ (yoneda.map (Limits.pullback.snd ψ τ)) a) = v' ∧
          pointsMap B S hS _ m (pointsMap B S hS _ p₁ a) = z := by
    intro z hz
    obtain ⟨q, rfl⟩ := hpS z
    obtain ⟨a, ha₁, ha₂⟩ := exists_points_of_isPullback_yoneda_map (sqP.map yoneda) q v'
      (by rw [← hpψ, pointsMap_comp_apply]; exact hz.trans hτv.symm)
    exact ⟨a, ha₂, by rw [← pointsMap_comp_apply, hp₁m, pointsMap_comp_apply, ha₁]⟩
  obtain ⟨a, ha, hax⟩ := hlift x hx
  obtain ⟨b, hb, hby⟩ := hlift y hy
  rw [← hby, ← hkey b hb]
  refine mem_of_mem_of_forall_isClopen_eq_preimage (A := {a | pointsToScheme B S hS _ a ∈ A})
    hdesc (etale_map_comp (κ := τ) (τ := j) hτs hj) sqX₁
    (isClosed_of_universallyClosed B S hS hYT' _ hg₁.2.2)
    (surjective_pointsMap_of_isPullback B S hS sqp₁.flip hpS)
    (isClosed_of_universallyClosed B S hS hX₁ p₁
      (universallyClosed_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS X'') hX₁ hX' p m hpC sqp₁))
    ⟨hAcl.preimage (schemePointsHomeomorph B S hS _).continuous,
      A.isOpen.preimage (schemePointsHomeomorph B S hS _).continuous⟩
    (fun a' b' ha' hab ha'A => ?_) ((hkey a ha).2 (by rwa [hax])) ((hover a).trans ha)
    ((hover b).trans hb)
  have hb' := ha'
  rw [hab, hover] at hb'
  rw [hover] at ha'
  refine (hkey b' hb').2 ?_
  rw [← hab]
  exact (hkey a' ha').1 ha'A

/-- **The fibre over an étale neighbourhood from an affine scheme.**  Let `g : X ⟶ h_W` be
proper and let `j : W' ⟶ W` be étale with `W'` affine.  If clopen sets of points descend along
étale base change of `g`, then two open sets `u`, `v` of points of `X` separating the fibre over
`j w'` cannot both meet it: the fibre lies in `u` as soon as one of its points does. -/
theorem mem_of_mem_of_isOpen_separating_fibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} {g : X ⟶ yoneda.obj W} (hg : IsProper B S hS g)
    (hdesc : ∀ (T : BigFppfOver B S hS) (τ : T ⟶ W),
      Etale ((BigFppfOver.toScheme B S hS).map τ) →
      ∀ A : Set (points B S hS (pullback g (yoneda.map τ))), IsClopen A →
        ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x, x ∈ A ↔
          pointsToScheme B S hS T (pointsMap B S hS _ (pullback.snd g (yoneda.map τ)) x) ∈ D)
    {R : CommRingCat.{u}} (hR : B.Contains (Spec R)) (h : B.obj hR ⟶ B.obj hS)
    (j : Over.mk h ⟶ W) (hj : Etale ((BigFppfOver.toScheme B S hS).map j))
    (w' : (BigFppfOver.toScheme B S hS).obj (Over.mk h)) {u v : Set (points B S hS X)}
    (hu : IsOpen u) (hv : IsOpen v)
    (huv : ∀ x, pointsToScheme B S hS W (pointsMap B S hS X g x) =
      (BigFppfOver.toScheme B S hS).map j w' → (x ∈ u ↔ x ∉ v))
    {x y : points B S hS X}
    (hx : pointsToScheme B S hS W (pointsMap B S hS X g x) =
      (BigFppfOver.toScheme B S hS).map j w')
    (hy : pointsToScheme B S hS W (pointsMap B S hS X g y) =
      (BigFppfOver.toScheme B S hS).map j w')
    (hxu : x ∈ u) : y ∈ u := by
  have hYW := isAlgebraicSpace_yoneda B S hS W
  have hYW' := isAlgebraicSpace_yoneda B S hS (Over.mk h)
  have sqX' := IsPullback.of_hasPullback g (yoneda.map j)
  have hX' := isAlgebraicSpace_pullback B S hS g (yoneda.map j) hX hYW' hYW
  have hg' := isProper_of_isPullback B S hS hX' hX hYW' hYW sqX' hg
  obtain ⟨X'', ψ, p, hpP, hpS, hpψ, -⟩ :=
    exists_chowSchemeCover_over_base B S hS R hR h hX' _ hg'.1 hg'.2.1
  have hψ : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ψ) := by
    refine isProper_toScheme_map_of_isProper_yoneda_map B S hS ψ ?_
    rw [← hpψ]
    exact isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS X'') hX' hYW' p _ hpP hg'
  have hφc : Continuous fun c : ((BigFppfOver.toScheme B S hS).map ψ).fiber w' =>
      pointsMap B S hS _ p ((schemePointsHomeomorph B S hS X'').symm
        (((BigFppfOver.toScheme B S hS).map ψ).fiberι w' c)) :=
    (continuous_pointsMap B S hS p).comp ((schemePointsHomeomorph B S hS X'').symm.continuous.comp
      (((BigFppfOver.toScheme B S hS).map ψ).fiberι w').continuous)
  have hφ : ∀ c, pointsToScheme B S hS _ (pointsMap B S hS _ (pullback.snd g (yoneda.map j))
      (pointsMap B S hS _ p ((schemePointsHomeomorph B S hS X'').symm
        (((BigFppfOver.toScheme B S hS).map ψ).fiberι w' c)))) = w' := by
    intro c
    rw [← pointsMap_comp_apply, hpψ, pointsToScheme_pointsMap_yoneda,
      ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]
    exact (((BigFppfOver.toScheme B S hS).map ψ).range_fiberι w').le ⟨c, rfl⟩
  have hover : ∀ x', pointsToScheme B S hS _
      (pointsMap B S hS _ (pullback.snd g (yoneda.map j)) x') = w' →
      pointsToScheme B S hS W (pointsMap B S hS X g
        (pointsMap B S hS _ (pullback.fst g (yoneda.map j)) x')) =
          (BigFppfOver.toScheme B S hS).map j w' := by
    intro x' hx'
    rw [← pointsMap_comp_apply, sqX'.w, pointsMap_comp_apply, pointsToScheme_pointsMap_yoneda,
      hx']
  obtain ⟨x', hx'₁, hx'₂⟩ := exists_points_of_isPullback_yoneda_map sqX' x w' hx
  obtain ⟨y', hy'₁, hy'₂⟩ := exists_points_of_isPullback_yoneda_map sqX' y w' hy
  rw [← hy'₁]
  exact mem_of_mem_of_isClopen_preimage_fiberι hX hg hdesc j hj ψ hψ p hpψ hpS hpP.2.2 w'
    (U := pointsMap B S hS _ (pullback.fst g (yoneda.map j)) ⁻¹' u)
    (isClopen_preimage_of_forall_mem_iff_notMem hφc
      (hu.preimage (continuous_pointsMap B S hS _)) (hv.preimage (continuous_pointsMap B S hS _))
      fun c => huv _ (hover _ (hφ c)))
    hx'₂ hy'₂ (by rw [Set.mem_preimage, hx'₁]; exact hxu)

/-- **The fibres of a proper morphism to a scheme are preconnected when clopen sets of points
descend along étale base change.**  Let `g : X ⟶ h_W` be a proper morphism from an algebraic
space `X` to the presheaf represented by an object `W` of the site.  Suppose that for every
morphism `τ : T ⟶ W` of the site which is étale on underlying schemes, every open and closed set
of points of `X ×_W T` is the preimage, under the projection, of a set of points of the scheme
`T`.  Then for every point `w` of the scheme `W`, the set of points of `X` lying over `w` is
preconnected. -/
theorem isPreconnected_fibre_of_forall_isClopen_eq_preimage
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (g : X ⟶ yoneda.obj W) (hg : IsProper B S hS g)
    (hdesc : ∀ (T : BigFppfOver B S hS) (τ : T ⟶ W),
      Etale ((BigFppfOver.toScheme B S hS).map τ) →
      ∀ A : Set (points B S hS (pullback g (yoneda.map τ))), IsClopen A →
        ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x, x ∈ A ↔
          pointsToScheme B S hS T (pointsMap B S hS _ (pullback.snd g (yoneda.map τ)) x) ∈ D)
    (w : (BigFppfOver.toScheme B S hS).obj W) :
    _root_.IsPreconnected
      {x : points B S hS X | pointsToScheme B S hS W (pointsMap B S hS X g x) = w} := by
  set Z := {x : points B S hS X | pointsToScheme B S hS W (pointsMap B S hS X g x) = w}
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hZuv hZ0
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨y₀, hy₀Z, hy₀u⟩, ⟨x₀, hx₀Z, hx₀v⟩⟩ := hcon
  have hsep : ∀ z ∈ Z, z ∈ u ↔ z ∉ v := fun z hz =>
    ⟨fun hzu hzv => (Set.eq_empty_iff_forall_notMem.mp hZ0 z) ⟨hz, hzu, hzv⟩,
      fun hzv => (hZuv hz).resolve_right hzv⟩
  obtain ⟨W₀, hW₀, hwW₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset
      (show w ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj W).Opens) from trivial)
  have hA : B.Contains (Spec Γ((BigFppfOver.toScheme B S hS).obj W, W₀)) :=
    Scheme.size_lt_of_isOpenImmersion hW₀.fromSpec W.left.property
  have hjw : hW₀.fromSpec (hW₀.primeIdealOf ⟨w, hwW₀⟩) = w :=
    hW₀.fromSpec_primeIdealOf ⟨w, hwW₀⟩
  exact hy₀u (mem_of_mem_of_isOpen_separating_fibre hX hg hdesc hA
    ((⟨hW₀.fromSpec⟩ : B.obj hA ⟶ W.left) ≫ W.hom) (siteObjectOverHom W hA hW₀.fromSpec)
    (inferInstance : Etale hW₀.fromSpec) (hW₀.primeIdealOf ⟨w, hwW₀⟩) hu hv
    (fun z hz => hsep z (hz.trans hjw)) (hx₀Z.trans hjw.symm) (hy₀Z.trans hjw.symm)
    ((hsep x₀ hx₀Z).2 hx₀v))

end AlgebraicGeometry.Space

end

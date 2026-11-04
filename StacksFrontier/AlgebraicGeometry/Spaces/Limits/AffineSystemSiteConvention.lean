module

public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps

/-!
# The site convention for a cofiltered system of affine schemes with limit in the site

Let `T = lim Tᵢ` be the limit of a cofiltered inverse system of affine objects `Tᵢ` of the big
fppf site of `S`, the limit taken in schemes, with `T` an object of the site. This is the
situation of Stacks 07XL. The represented presheaves `yoneda Tᵢ` form an inverse system of
algebraic spaces with affine transition morphisms, and this file proves that this system satisfies
the chapter's standing convention of Section 70.2 (tag 07SD), in the form
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` in which the descent results of the
chapter consume it. Nothing is assumed of the size of the index.

The convention asks that, for a stage `i`, an affine object `Z` of the site and a morphism
`Z ⟶ Tᵢ`, the limit in schemes of the base changes `Z ×_{Tᵢ} T_k` over the stages `k ⟶ i` lies
in the site. That limit is a subobject of `Z ×_{Tᵢ} T`: the limit in schemes maps to `Z` through
any stage, and to `T` because `T` is the limit of the stages above `i`, and two morphisms into it
which agree after these two maps agree at every stage `Z ×_{Tᵢ} T_k`, each of which is a fibre
product. The comparison is a morphism of affine schemes, hence quasi-compact, so by Stacks 04VA
the limit is no larger than `Z ×_{Tᵢ} T`, which is in the site by Stacks 000R (1).

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_isLimit`: the convention for the
  system `yoneda Tᵢ`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {J : Type u} [Category.{u} J] [IsCofiltered J]

/-- A monomorphism of affine schemes into a fibre product of affine schemes of size below `κ`
has source of size below `κ`. -/
theorem size_lt_of_mono_pullback {κ : Cardinal.{u}} {X P Q R : Scheme.{u}} [IsAffine X]
    [IsAffine P] [IsAffine Q] [IsAffine R] (f : P ⟶ R) (g : Q ⟶ R) (m : X ⟶ pullback f g)
    [Mono m] (hP : P.size < κ) (hQ : Q.size < κ) : X.size < κ := by
  have : _root_.AlgebraicGeometry.IsAffineHom g := isAffineHom_of_isAffine g
  have : IsAffine (pullback f g) := IsAffine.of_isPullback (IsPullback.of_hasPullback f g)
  have : _root_.AlgebraicGeometry.IsAffineHom m := isAffineHom_of_isAffine m
  exact (Scheme.size_le_of_mono_quasiCompact m).trans_lt (Scheme.size_pullback_lt f g hP hQ)

omit [IsCofiltered J] in
/-- If `W` is identified, after `yoneda`, with the base change along `g` of the system `D` over
`i`, then every `W k` is the fibre product `Z ×_{Tᵢ} T_k` in the site, through stage maps
compatible with the transition morphisms. -/
theorem exists_isPullback_baseChange_stage (D : J ⥤ BigAffineFppf B S hS) (i : J)
    (Z : BigAffineFppf B S hS) (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙ yoneda).obj i)
    (W : Over i ⥤ BigAffineFppf B S hS)
    (hiso : W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
      (Over.post (X := i) (D ⋙ BigAffineFppf.inclusion B S hS ⋙ yoneda) ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) :
    ∃ (a : ∀ k : Over i, (BigAffineFppf.inclusion B S hS).obj (W.obj k) ⟶
        (BigAffineFppf.inclusion B S hS).obj (D.obj k.left))
      (b : ∀ k : Over i, (BigAffineFppf.inclusion B S hS).obj (W.obj k) ⟶
        (BigAffineFppf.inclusion B S hS).obj Z),
      (∀ k : Over i, IsPullback (a k) (b k)
        ((BigAffineFppf.inclusion B S hS).map (D.map k.hom)) (yoneda.preimage g)) ∧
      (∀ {k k' : Over i} (u : k ⟶ k'),
        (BigAffineFppf.inclusion B S hS).map (W.map u) ≫ b k' = b k) ∧
      (∀ {k k' : Over i} (u : k ⟶ k'), (BigAffineFppf.inclusion B S hS).map (W.map u) ≫ a k' =
        a k ≫ (BigAffineFppf.inclusion B S hS).map (D.map u.left)) := by
  let ι := BigAffineFppf.inclusion B S hS
  let E := D ⋙ ι ⋙ yoneda
  let g' : ι.obj Z ⟶ ι.obj (D.obj i) := yoneda.preimage g
  -- The diagram of base changes and its two projections.
  let G := (Over.post (X := i) E ⋙ Over.pullback g) ⋙ Over.forget (yoneda.obj (ι.obj Z))
  let fstP : ∀ k : Over i, G.obj k ⟶ E.obj k.left := fun k => pullback.fst (E.map k.hom) g
  let sndP : ∀ k : Over i, G.obj k ⟶ yoneda.obj (ι.obj Z) := fun k =>
    ((Over.post (X := i) E ⋙ Over.pullback g).obj k).hom
  have hsq : ∀ k : Over i, IsPullback (fstP k) (sndP k) (E.map k.hom) g := fun k =>
    IsPullback.of_hasPullback (E.map k.hom) g
  have hsndNat : ∀ {k k' : Over i} (u : k ⟶ k'), G.map u ≫ sndP k' = sndP k := fun u =>
    Over.w ((Over.post (X := i) E ⋙ Over.pullback g).map u)
  have hfstNat : ∀ {k k' : Over i} (u : k ⟶ k'),
      G.map u ≫ fstP k' = fstP k ≫ E.map u.left := by
    intro k k' u
    change pullback.lift (pullback.fst _ _ ≫ ((Over.post (X := i) E).map u).left)
      (pullback.snd _ _) _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]
    rfl
  have hWnat : ∀ {k k' : Over i} (u : k ⟶ k'),
      yoneda.map (ι.map (W.map u)) ≫ hiso.hom.app k' = hiso.hom.app k ≫ G.map u :=
    fun u => hiso.hom.naturality u
  -- The stage maps `W k ⟶ T_k` and `W k ⟶ Z`.
  let a : ∀ k : Over i, ι.obj (W.obj k) ⟶ ι.obj (D.obj k.left) := fun k =>
    yoneda.preimage (hiso.hom.app k ≫ fstP k)
  let b : ∀ k : Over i, ι.obj (W.obj k) ⟶ ι.obj Z := fun k =>
    yoneda.preimage (hiso.hom.app k ≫ sndP k)
  have ha : ∀ k, yoneda.map (a k) = hiso.hom.app k ≫ fstP k := fun k => yoneda.map_preimage _
  have hb : ∀ k, yoneda.map (b k) = hiso.hom.app k ≫ sndP k := fun k => yoneda.map_preimage _
  -- Each stage is a fibre product, in the site.
  have hpbPsh : ∀ k : Over i, IsPullback (yoneda.map (a k)) (yoneda.map (b k))
      (yoneda.map (ι.map (D.map k.hom))) (yoneda.map g') := by
    intro k
    rw [ha, hb, yoneda.map_preimage g]
    exact (hsq k).of_iso (hiso.app k).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp)
  refine ⟨a, b, fun k => IsPullback.of_map yoneda (yoneda.map_injective (by
      simpa only [Functor.map_comp] using (hpbPsh k).w)) (hpbPsh k), fun u => ?_, fun u => ?_⟩
  · apply yoneda.map_injective
    rw [Functor.map_comp, hb, hb, ← Category.assoc, hWnat u, Category.assoc, hsndNat]
  · apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, ha, ha, ← Category.assoc, hWnat u, Category.assoc,
      hfstNat, Category.assoc]
    rfl

/-- Given stage maps exhibiting each `W k` as the fibre product `Z ×_{Tᵢ} T_k`, compatibly with
the transitions, the limit in schemes of the `W k` admits a monomorphism into `Z ×_{Tᵢ} T`,
where `T` is the limit of the system `D`. -/
theorem exists_mono_pullback_of_isPullback_stage (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) {i : J}
    {Z : BigAffineFppf B S hS}
    (g' : (BigAffineFppf.inclusion B S hS).obj Z ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i))
    (W : Over i ⥤ BigAffineFppf B S hS)
    (a : ∀ k : Over i, (BigAffineFppf.inclusion B S hS).obj (W.obj k) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.obj k.left))
    (b : ∀ k : Over i, (BigAffineFppf.inclusion B S hS).obj (W.obj k) ⟶
      (BigAffineFppf.inclusion B S hS).obj Z)
    (hpb : ∀ k : Over i,
      IsPullback (a k) (b k) ((BigAffineFppf.inclusion B S hS).map (D.map k.hom)) g')
    (hbnat : ∀ {k k' : Over i} (u : k ⟶ k'),
      (BigAffineFppf.inclusion B S hS).map (W.map u) ≫ b k' = b k)
    (hanat : ∀ {k k' : Over i} (u : k ⟶ k'),
      (BigAffineFppf.inclusion B S hS).map (W.map u) ≫ a k' =
        a k ≫ (BigAffineFppf.inclusion B S hS).map (D.map u.left))
    {c' : Cone (underlyingDiagram (W ⋙ BigAffineFppf.inclusion B S hS))} (hc' : IsLimit c') :
    ∃ m : c'.pt ⟶ pullback ((BigFppfOver.toScheme B S hS).map g')
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))),
      Mono m := by
  let F := BigFppfOver.toScheme B S hS
  let ι := BigAffineFppf.inclusion B S hS
  have : PreservesLimitsOfShape WalkingCospan F := by
    apply comp_preservesLimitsOfShape
  have hpbSch : ∀ k : Over i,
      IsPullback (F.map (a k)) (F.map (b k)) (F.map (ι.map (D.map k.hom))) (F.map g') :=
    fun k => (hpb k).map F
  -- `T` is the limit of the stages above `i`.
  have hT : IsLimit (((BigAffineFppf.toScheme B S hS).mapCone c).whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc
  let k₀ : Over i := Over.mk (𝟙 i)
  -- The comparison from the limit in schemes to `Z ×_{Tᵢ} T`.
  let toT : c'.pt ⟶ F.obj (ι.obj c.pt) := hT.lift
    { pt := c'.pt
      π :=
        { app := fun k => c'.π.app k ≫ F.map (a k)
          naturality := by
            intro k k' u
            have hw : c'.π.app k ≫ F.map (ι.map (W.map u)) = c'.π.app k' := c'.w u
            change 𝟙 c'.pt ≫ c'.π.app k' ≫ F.map (a k') =
              (c'.π.app k ≫ F.map (a k)) ≫ F.map (ι.map (D.map u.left))
            rw [Category.id_comp, Category.assoc, ← F.map_comp, ← hanat u, F.map_comp,
              ← Category.assoc, hw] } }
  have htoT : ∀ k : Over i, toT ≫ F.map (ι.map (c.π.app k.left)) = c'.π.app k ≫ F.map (a k) :=
    fun k => hT.fac _ k
  let toZ : c'.pt ⟶ F.obj (ι.obj Z) := c'.π.app k₀ ≫ F.map (b k₀)
  have htoT₀ : toT ≫ F.map (ι.map (c.π.app i)) = c'.π.app k₀ ≫ F.map (a k₀) := htoT k₀
  have hcomm : toZ ≫ F.map g' = toT ≫ F.map (ι.map (c.π.app i)) := by
    have hid : F.map (ι.map (D.map k₀.hom)) = 𝟙 _ := by simp [k₀]
    rw [htoT₀]
    simp only [toZ, Category.assoc]
    rw [← (hpbSch k₀).w, hid, Category.comp_id]
  have hZk : ∀ k : Over i, c'.π.app k ≫ F.map (b k) = toZ := by
    intro k
    let u : k ⟶ k₀ := Over.homMk k.hom (by simp [k₀])
    have hw : c'.π.app k ≫ F.map (ι.map (W.map u)) = c'.π.app k₀ := c'.w u
    simp only [toZ, ← hw, Category.assoc, ← F.map_comp,
      show ι.map (W.map u) ≫ b k₀ = b k from hbnat u]
  refine ⟨pullback.lift toZ toT hcomm, ⟨fun {U} x y hxy => hc'.hom_ext fun k => ?_⟩⟩
  have h1 := congrArg (· ≫ pullback.fst _ _) hxy
  have h2 := congrArg (· ≫ pullback.snd _ _) hxy
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h1 h2
  refine (hpbSch k).hom_ext ?_ (by simpa only [Category.assoc, hZk k] using h1)
  simpa only [Category.assoc, htoT k] using congrArg (· ≫ F.map (ι.map (c.π.app k.left))) h2

/-- **The site convention of Section 70.2 (tag 07SD) for a system of affine schemes whose limit
lies in the site.** If `T = lim Tᵢ` is the limit in schemes of a cofiltered inverse system of
affine objects of the big fppf site of `S`, and `T` is an object of the site, then the system of
represented presheaves `yoneda Tᵢ` satisfies
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. No condition on the size of the index is
needed. -/
theorem siteContainsBaseChangeLimits_of_isLimit (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    SiteContainsBaseChangeLimits B S hS (D ⋙ BigAffineFppf.inclusion B S hS ⋙ yoneda) := by
  intro i Z g W hiso c' hc'
  obtain ⟨a, b, hpb, hbnat, hanat⟩ := exists_isPullback_baseChange_stage D i Z g W hiso
  obtain ⟨m, hm⟩ := exists_mono_pullback_of_isPullback_stage D hc _ W a b hpb hbnat hanat hc'
  have : ∀ k, IsAffine ((underlyingDiagram (W ⋙ BigAffineFppf.inclusion B S hS)).obj k) :=
    fun k => (W.obj k).property
  have : IsAffine c'.pt := Scheme.isAffine_of_isLimit _ hc'
  have : ∀ X : BigAffineFppf B S hS, IsAffine
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj X)) :=
    fun X => X.property
  exact size_lt_of_mono_pullback _ _ m ((BigAffineFppf.inclusion B S hS).obj Z).left.property
    ((BigAffineFppf.inclusion B S hS).obj c.pt).left.property

end AlgebraicGeometry.Space

end

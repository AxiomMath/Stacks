module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismAgreementOnFlatAdicSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace

/-!
# Glueing a morphism out of an affine base along the fpqc covering by `U` and a flat chart

Let `V` be a locally Noetherian object of the big fppf site of `S`, let `T` be a closed set of
points of `V` with open complement `U`, let `f : X' ⟶ V` be a morphism whose base change
`f⁻¹(U) ⟶ U` is an isomorphism, and let `(w', ŵ)` be a compatible pair of morphisms
`X' ⟶ W`, `V_{/T} ⟶ W` to an algebraic space `W`. Let `κ : Vh ⟶ V` be a flat, quasi-compact
morphism of the site whose image contains `T` — in the application `Vh = Spec Â` for the
completion `Â` of the ring of `V` along an ideal cutting out `T` — and let `h : Vh ⟶ W` be a
morphism inducing `ŵ` along `κ`. This file glues `h` with the morphism `U ≅ f⁻¹(U) ⟶ W`
induced by `w'` to a morphism `w : V ⟶ W` with `morToModificationCompletion f T W w = (w', ŵ)`,
which is step F4 of the existence half of [Stacks, Tag 0GI3]. It also derives the cocycle
condition on `Vh ×_V Vh` needed there from step F3 when `Vh` is the spectrum of a flat
Noetherian algebra over the ring of an affine `V`.

## Main results

* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_flat_cover`: the glueing.
* `AlgebraicGeometry.Space.yoneda_map_comp_eq_of_comp_eq_of_flat_spectrum`: the cocycle
  condition on `Spec (R ⊗_A R)` for a flat Noetherian `A`-algebra `R`.
* `AlgebraicGeometry.Space.zeroLocus_subset_range_specAdicCompletion`,
  `AlgebraicGeometry.Space.flat_specAdicCompletion`,
  `AlgebraicGeometry.Space.quasiCompact_specAdicCompletion`: for the `I`-adic completion `Â` of
  the ring of an affine scheme `X`, the morphism `Spec Â ⟶ X` hits `V(I)` and is flat (for a
  Noetherian ring) and quasi-compact, so that it may serve as `κ` above.

## Implementation notes

*The covering.* The open complement `U` of `T` is an object `U_V` of the site
(`AlgebraicGeometry.Space.openSiteObject`), and the family `{U_V ⟶ V, κ}` is a covering of the
fpqc precoverage: both members are flat, the open immersion is quasi-compact because `V` is
locally Noetherian, and the family is jointly surjective because the image of `κ` contains `T`.
An algebraic space is a sheaf for the fpqc topology (Stacks 0APL,
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc`), so `W` glues sections along it.

*Compatibility.* The compatibility condition of the family is tested on arbitrary pairs of
morphisms from an object of the site, not on fibre products. Two morphisms into `U_V` agreeing
in `V` are equal. A morphism into `U_V` and one into `Vh` agreeing in `V` are handled by the
hypothesis `hX'h` (step F2: `h` and `w'` agree on `X' ×_V Vh`), applied to the section of `f`
over `U`. Two morphisms into `Vh` agreeing in `V` are handled by the hypothesis `hhh`.

*The two components.* That `f ≫ w = w'` and that `w` induces `ŵ` are both tested on the
pullback of the covering sieve to an arbitrary object of the site, on which `W` is separated:
over `U_V` one uses that `f` is an isomorphism over `U` and the compatibility of `(w', ŵ)`, over
`Vh` the hypotheses on `h`.

*The cocycle condition.* For `Vh = Spec R` with `R` a flat Noetherian algebra over the ring `A`
of an affine `V`, two morphisms `z₁, z₂ : Z ⟶ Vh` agreeing in `V` factor through
`Spec (R ⊗_A R)`, and the two composites `Spec (R ⊗_A R) ⟶ Vh ⟶ W` are equal by
`AlgebraicGeometry.Space.eq_of_eq_off_zeroLocus_of_eq_on_quotients_of_isProper` (step F3) with
`D = R ⊗_A R`, flat over `R` through the left factor: off `V(I D)` both composites factor
through `U` (by `hX'h`), on every `Spec (D / I ^ n D)` both are given by `ŵ` (by the hypothesis on
`h`), and after the proper base change `X' ×_V Spec D ⟶ Spec D`, which is an isomorphism over
`U`, both equal the composite with `w'` (by `hX'h` again).

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology


/-- The morphism from a representable presheaf attached to a morphism of the site. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {Z V : BigFppfOver B S hS} (z : Z ⟶ V) :
    yonedaEquiv.symm z = yoneda.map z :=
  yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map z).symm

/-- A morphism of the site into `V` whose image misses the image of `T` lifts into the open
subspace of `yoneda V` with point set `Tᶜ`. -/
private theorem exists_lift_compl_of_range_subset (V : BigFppfOver B S hS)
    (T : Set (points B S hS (yoneda.obj V))) {Zo : BigFppfOver B S hS} (z : Zo ⟶ V)
    (hz : ∀ y, (BigFppfOver.toScheme B S hS).map z y ∉ pointsToScheme B S hS V '' T) :
    ∃ u : yoneda.obj Zo ⟶ (openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ).toFunctor,
      u ≫ (openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ).ι = yoneda.map z := by
  refine (exists_factor_openSubspaceOfPoints_iff B S hS Tᶜ (yoneda.map z)).mpr ?_
  rintro _ ⟨y, rfl⟩ hyT
  refine hz (pointsToScheme B S hS Zo y) ⟨_, hyT, ?_⟩
  exact pointsToScheme_pointsMap_yoneda B S hS z y

/-- The section `inv (snd) ≫ fst` of an isomorphic base change lies over `g`. -/
private theorem inv_snd_comp_fst_comp {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [IsIso (pullback.snd f g)] :
    (inv (pullback.snd f g) ≫ pullback.fst f g) ≫ f = g := by
  simp only [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- `ŵ` on a point of the completion only depends on the underlying morphism. -/
private theorem completion_app_congr (V : BigFppfOver B S hS)
    (T : Set (points B S hS (yoneda.obj V))) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ŵ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {Y : BigFppfOver B S hS} {z z' : Y ⟶ V} (hz : HasImageIn B S hS (yoneda.obj V) T Y z)
    (hz' : HasImageIn B S hS (yoneda.obj V) T Y z') (h : z = z') :
    ŵ.app (op Y) ⟨ULift.up z, hz⟩ = ŵ.app (op Y) ⟨ULift.up z', hz'⟩ := by
  subst h
  rfl

/-- **Glueing along the fpqc covering by `U` and a flat chart (step F4 of Stacks 0GI3).** Let
`V` be a locally Noetherian object of the site, `T` a closed set of points of `V` with open
complement `U`, `f : X' ⟶ V` a morphism with `f⁻¹(U) ⟶ U` an isomorphism, and `(w', ŵ)` a
compatible pair. Let `κ : Vh ⟶ V` be flat and quasi-compact with image containing `T`, and let
`h : Vh ⟶ W` induce `ŵ` along `κ` on morphisms with image in `T`, agree with `w'` on
`X' ×_V Vh`, and satisfy the cocycle condition on `Vh ×_V Vh`. Then some `w : V ⟶ W` has
restriction `w'` to `X'` and induces `ŵ`. -/
theorem exists_morToModificationCompletion_eq_of_flat_cover
    {X' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (V : BigFppfOver B S hS) [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    {T : Set (points B S hS (yoneda.obj V))} (hT : IsClosed T)
    (f : X' ⟶ yoneda.obj V)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ).ι))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    {Vh : BigFppfOver B S hS} (κ : Vh ⟶ V)
    (hκflat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map κ))
    (hκqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map κ))
    (hκsurj : ∀ x ∈ T,
      pointsToScheme B S hS V x ∈ Set.range ((BigFppfOver.toScheme B S hS).map κ))
    (h : yoneda.obj Vh ⟶ W)
    (hh : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ Vh)
      (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ κ)),
      h.app (op Zo) z = (ŵ.app (op Zo) ⟨ULift.up (z ≫ κ), hz⟩).down)
    (hX'h : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ : Z ⟶ X') (g₂ : Z ⟶ yoneda.obj Vh),
      g₁ ≫ f = g₂ ≫ yoneda.map κ → g₁ ≫ w' = g₂ ≫ h)
    (hhh : ∀ (Zo : BigFppfOver B S hS) (z₁ z₂ : Zo ⟶ Vh), z₁ ≫ κ = z₂ ≫ κ →
      yoneda.map z₁ ≫ h = yoneda.map z₂ ≫ h) :
    ∃ w : yoneda.obj V ⟶ W, morToModificationCompletion B S hS f T W w = (w', ŵ) := by
  classical
  let U := openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ
  -- the section of `f` over `U`
  let sU : U.toFunctor ⟶ X' := inv (pullback.snd f U.ι) ≫ pullback.fst f U.ι
  have hsU : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ X') (u : Z ⟶ U.toFunctor),
      x ≫ f = u ≫ U.ι → x = u ≫ sU := by
    intro Z x u hxu
    calc x = pullback.lift x u hxu ≫ pullback.fst f U.ι := (pullback.lift_fst _ _ _).symm
      _ = u ≫ sU := by
        conv_rhs => rw [← pullback.lift_snd x u hxu]
        simp only [sU, Category.assoc, IsIso.hom_inv_id_assoc]
  have hsUf : sU ≫ f = U.ι := inv_snd_comp_fst_comp f U.ι
  -- the open complement of `T` as an object of the site
  have hTs : IsClosed (pointsToScheme B S hS V '' T) :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V T).mp hT
  obtain ⟨O, hOeq⟩ : ∃ O : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      (O : Set ((BigFppfOver.toScheme B S hS).obj V)) = (pointsToScheme B S hS V '' T)ᶜ :=
    ⟨⟨_, hTs.isOpen_compl⟩, rfl⟩
  let Uo := openSiteObject B S hS V O
  let ι : Uo ⟶ V := openSiteObjectHom B S hS V O
  have hι : (BigFppfOver.toScheme B S hS).map ι = O.ι := map_openSiteObjectHom B S hS V O
  obtain ⟨uι, huι⟩ : ∃ u : yoneda.obj Uo ⟶ U.toFunctor, u ≫ U.ι = yoneda.map ι := by
    refine exists_lift_compl_of_range_subset B S hS V T ι fun y => ?_
    rw [hι]
    have hy : O.ι y ∈ (O : Set ((BigFppfOver.toScheme B S hS).obj V)) := by
      rw [← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩
    rw [hOeq] at hy
    exact hy
  -- the covering family
  let X : Bool → BigFppfOver B S hS := fun b => cond b Uo Vh
  let π : ∀ b, X b ⟶ V := fun b => Bool.rec (motive := fun b => X b ⟶ V) κ ι b
  have hcov : Presieve.ofArrows X π ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)) V := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    have hflat : ∀ b, AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (π b)) := by
      intro b
      cases b
      · exact hκflat
      · show AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map ι)
        rw [hι]
        exact (inferInstance : AlgebraicGeometry.Flat O.ι)
    let 𝒰 : Scheme.Cover (Scheme.precoverage @AlgebraicGeometry.Flat)
        ((BigFppfOver.toScheme B S hS).obj V) :=
      Scheme.Cover.mkOfCovers Bool (fun b => (BigFppfOver.toScheme B S hS).obj (X b))
        (fun b => (BigFppfOver.toScheme B S hS).map (π b)) (fun x => by
          by_cases hx : x ∈ (O : Set ((BigFppfOver.toScheme B S hS).obj V))
          · refine ⟨true, ⟨x, hx⟩, ?_⟩
            show (BigFppfOver.toScheme B S hS).map ι ⟨x, hx⟩ = x
            rw [hι]
            rfl
          · have hx' : x ∈ pointsToScheme B S hS V '' T := by
              rw [hOeq] at hx
              exact not_not.mp hx
            obtain ⟨t, htT, rfl⟩ := hx'
            obtain ⟨y, hy⟩ := hκsurj t htT
            exact ⟨false, y, hy⟩) hflat
    have hqc : ∀ b, AlgebraicGeometry.QuasiCompact (𝒰.f b) := by
      intro b
      cases b
      · exact hκqc
      · show AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ι)
        rw [hι]
        exact (inferInstance : AlgebraicGeometry.QuasiCompact O.ι)
    have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
      @AlgebraicGeometry.QuasiCompactCover.of_finite _ _ 𝒰
        Scheme.instJointlySurjectivePrecoverage hqc (inferInstanceAs (Finite Bool))
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr this, 𝒰.mem₀⟩
  -- `W` is a sheaf for the fpqc topology
  have hWs : Presieve.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) W :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hW.isSheaf_fpqc
  have hgen := Precoverage.generate_mem_toGrothendieck hcov
  have hsheafFor : (Presieve.ofArrows X π).IsSheafFor W :=
    (Presieve.isSheafFor_iff_generate _).mpr (hWs _ hgen)
  -- `W` is separated for the pullback of the covering to any object over `V`
  have hsep : ∀ (Zo : BigFppfOver B S hS) (zV : Zo ⟶ V) (t₁ t₂ : W.obj (op Zo)),
      (∀ (Y : BigFppfOver B S hS) (g : Y ⟶ Zo) (b : Bool) (e : Y ⟶ X b),
        g ≫ zV = e ≫ π b → W.map g.op t₁ = W.map g.op t₂) → t₁ = t₂ := by
    intro Zo zV t₁ t₂ hagree
    refine (hWs _ (GrothendieckTopology.pullback_stable _ zV hgen)).isSeparatedFor.ext ?_
    intro Y g hg
    obtain ⟨Y', e, k, hk, hek⟩ := hg
    cases hk with
    | mk b => exact hagree Y g b e hek.symm
  -- the family to glue
  let φ : ∀ b, yoneda.obj (X b) ⟶ W := fun b =>
    Bool.rec (motive := fun b => yoneda.obj (X b) ⟶ W) h (uι ≫ sU ≫ w') b
  have hmixed : ∀ (Zo : BigFppfOver B S hS) (g₁ : Zo ⟶ Uo) (g₂ : Zo ⟶ Vh),
      g₁ ≫ ι = g₂ ≫ κ → yoneda.map g₁ ≫ uι ≫ sU ≫ w' = yoneda.map g₂ ≫ h := fun Zo g₁ g₂ hg => by
    simpa only [Category.assoc] using hX'h (yoneda.map g₁ ≫ uι ≫ sU) (yoneda.map g₂) (by
      rw [Category.assoc, Category.assoc, hsUf, huι, ← Functor.map_comp, ← Functor.map_comp, hg])
  have hcompatible : Presieve.Arrows.Compatible W π (fun b => yonedaEquiv (φ b)) := by
    intro i j Zo gi gj hij
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    congr 1
    cases i <;> cases j
    · exact hhh Zo gi gj hij
    · exact (hmixed Zo gj gi hij.symm).symm
    · exact hmixed Zo gi gj hij
    · have hgg : gi = gj := BigFppfOver.map_toScheme_injective B S hS (by
        have := congrArg (BigFppfOver.toScheme B S hS).map hij
        change (BigFppfOver.toScheme B S hS).map (gi ≫ ι) =
          (BigFppfOver.toScheme B S hS).map (gj ≫ ι) at this
        rw [Functor.map_comp, Functor.map_comp, hι] at this
        exact (cancel_mono O.ι).mp this)
      rw [hgg]
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsheafFor _ hcompatible
  let w : yoneda.obj V ⟶ W := yonedaEquiv.symm t
  have hwb : ∀ b, yoneda.map (π b) ≫ w = φ b := by
    intro b
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact ht b
  have hwι : yoneda.map ι ≫ w = uι ≫ sU ≫ w' := hwb true
  have hwκ : yoneda.map κ ≫ w = h := hwb false
  refine ⟨w, Prod.ext ?_ ?_⟩
  · -- the restriction to `X'`
    show f ≫ w = w'
    refine hom_ext_yoneda fun Zo p => ?_
    have hzV : p ≫ f = yoneda.map (yonedaEquiv (p ≫ f)) := by
      rw [← yonedaEquiv_symm_eq_yoneda_map, Equiv.symm_apply_apply]
    apply yonedaEquiv.injective
    refine hsep Zo (yonedaEquiv (p ≫ f)) _ _ fun Y g b e hge => ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    congr 1
    have hgp : (yoneda.map g ≫ p) ≫ f = yoneda.map e ≫ yoneda.map (π b) := by
      rw [Category.assoc, hzV, ← Functor.map_comp, hge, Functor.map_comp]
    cases b
    · calc yoneda.map g ≫ p ≫ f ≫ w = ((yoneda.map g ≫ p) ≫ f) ≫ w := by
            simp only [Category.assoc]
        _ = yoneda.map e ≫ h := by
            rw [hgp, Category.assoc]
            exact congrArg (yoneda.map e ≫ ·) hwκ
        _ = yoneda.map g ≫ p ≫ w' := by
            rw [← Category.assoc]
            exact (hX'h _ _ hgp).symm
    · have hp : yoneda.map g ≫ p = (yoneda.map e ≫ uι) ≫ sU :=
        hsU _ _ (by rw [hgp, Category.assoc, huι])
      calc yoneda.map g ≫ p ≫ f ≫ w = ((yoneda.map g ≫ p) ≫ f) ≫ w := by
            simp only [Category.assoc]
        _ = yoneda.map e ≫ uι ≫ sU ≫ w' := by
            rw [hgp, Category.assoc]
            exact congrArg (yoneda.map e ≫ ·) hwι
        _ = yoneda.map g ≫ p ≫ w' := by
            rw [← Category.assoc (yoneda.map g) p w', hp]
            simp only [Category.assoc]
  · -- the induced morphism on the completion
    show (completionSubfunctor B S hS (yoneda.obj V) T).ι ≫
      Functor.whiskerRight w uliftFunctor.{u + 1} = ŵ
    ext Zo ⟨⟨zV⟩, hz⟩
    induction Zo using Opposite.rec with | op Zo => ?_
    apply ULift.ext
    show w.app (op Zo) zV = (ŵ.app (op Zo) ⟨ULift.up zV, hz⟩).down
    refine hsep Zo zV _ _ fun Y g b e hge => ?_
    have hgz : HasImageIn B S hS (yoneda.obj V) T Y (g ≫ zV) :=
      (completionSubfunctor B S hS (yoneda.obj V) T).map g.op hz
    have hnat : W.map g.op (ŵ.app (op Zo) ⟨ULift.up zV, hz⟩).down =
        (ŵ.app (op Y) ⟨ULift.up (g ≫ zV), hgz⟩).down :=
      congrArg ULift.down (NatTrans.naturality_apply ŵ g.op ⟨ULift.up zV, hz⟩).symm
    have hwnat : W.map g.op (w.app (op Zo) zV) = w.app (op Y) (g ≫ zV) :=
      (NatTrans.naturality_apply w g.op zV).symm
    rw [hnat, hwnat]
    cases b
    · have hez : HasImageIn B S hS (yoneda.obj V) T Y (e ≫ κ) := hge ▸ hgz
      rw [completion_app_congr B S hS V T ŵ hgz hez hge, ← hh Y e hez]
      have h3 : w.app (op Y) (g ≫ zV) = (yoneda.map κ ≫ w).app (op Y) e := by
        rw [hge]
        rfl
      rw [h3, hwκ]
    · -- the point of `X'` over `e ≫ ι`
      let x' : X'.obj (op Y) := sU.app (op Y) (uι.app (op Y) e)
      have hfx' : f.app (op Y) x' = g ≫ zV := by
        have h1 : f.app (op Y) x' = (uι ≫ sU ≫ f).app (op Y) e := rfl
        rw [h1, hsUf, huι, hge]
        rfl
      have hx' : HasImageIn B S hS X' (pointsMap B S hS X' f ⁻¹' T) Y x' := by
        rw [hasImageIn_iff_range_subset]
        rintro _ ⟨y, rfl⟩
        have h2 : HasImageIn B S hS (yoneda.obj V) T Y (f.app (op Y) x') := by
          rw [hfx']
          exact hgz
        rw [hasImageIn_iff_range_subset, ← yonedaEquiv_symm_naturality_right] at h2
        show pointsMap B S hS X' f _ ∈ T
        rw [← pointsMap_comp_apply]
        exact h2 ⟨y, rfl⟩
      have hfx'T : HasImageIn B S hS (yoneda.obj V) T Y (f.app (op Y) x') := by
        rw [hfx']
        exact hgz
      have hc := congrArg (fun α => ((α.app (op Y)) ⟨ULift.up x', hx'⟩).down) hcompat
      change (ŵ.app (op Y) ⟨ULift.up (f.app (op Y) x'), hfx'T⟩).down = w'.app (op Y) x' at hc
      rw [← completion_app_congr B S hS V T ŵ hfx'T hgz hfx', hc]
      have h3 : w.app (op Y) (g ≫ zV) = (yoneda.map ι ≫ w).app (op Y) e := by
        rw [hge]
        rfl
      rw [h3, hwι]
      rfl

/-- **The cocycle condition on `Spec (R ⊗_A R)` (from step F3 of Stacks 0GI3).** Let `V` be an
affine object of the site with ring `A`, `I ⊆ A` an ideal cutting out the closed set `T`,
`f : X' ⟶ V` a proper morphism from an algebraic space with `f⁻¹(U) ⟶ U` an isomorphism over the
complement `U` of `T`, and `ŵ : V_{/T} ⟶ W`, `w' : X' ⟶ W` morphisms to an algebraic space. Let
`κ : V̂ ⟶ V` be the spectrum of a flat `A`-algebra `R` which is a Noetherian ring, with
`Spec (R ⊗_A R)` in the site, and let `h : V̂ ⟶ W` induce `ŵ` along `κ` and agree with `w'` on
`X' ×_V V̂`. Then any two morphisms `z₁, z₂` into `V̂` agreeing in `V` satisfy
`z₁ ≫ h = z₂ ≫ h`. -/
theorem yoneda_map_comp_eq_of_comp_eq_of_flat_spectrum
    {X' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hW : IsAlgebraicSpace B S hS W)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {T : Set (points B S hS (yoneda.obj V))}
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (f : X' ⟶ yoneda.obj V) (hf : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ).ι))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) R]
    [Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) R]
    {Vh : BigFppfOver B S hS} (κ : Vh ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj Vh ≅ Spec (.of R))
    (hκ : (BigFppfOver.toScheme B S hS).map κ = e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) R)) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
    (hD : B.Contains (Spec (.of (TensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) R R))))
    (h : yoneda.obj Vh ⟶ W)
    (hh : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ Vh)
      (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ κ)),
      h.app (op Zo) z = (ŵ.app (op Zo) ⟨ULift.up (z ≫ κ), hz⟩).down)
    (hX'h : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ : Z ⟶ X') (g₂ : Z ⟶ yoneda.obj Vh),
      g₁ ≫ f = g₂ ≫ yoneda.map κ → g₁ ≫ w' = g₂ ≫ h)
    (Zo : BigFppfOver B S hS) (z₁ z₂ : Zo ⟶ Vh) (hz : z₁ ≫ κ = z₂ ≫ κ) :
    yoneda.map z₁ ≫ h = yoneda.map z₂ ≫ h := by
  classical
  let A := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  let D := TensorProduct A R R
  let J : Ideal D := (I.map (algebraMap A R)).map (algebraMap R D)
  let U := openSubspaceOfPoints B S hS (yoneda.obj V) Tᶜ
  -- the section of `f` over `U`
  let sU : U.toFunctor ⟶ X' := inv (pullback.snd f U.ι) ≫ pullback.fst f U.ι
  have hsUf : sU ≫ f = U.ι := inv_snd_comp_fst_comp f U.ι
  -- the two projections `Spec D ⟶ Spec R`
  let a₀ : Spec (.of R) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let j₁ : Spec (.of D) ⟶ Spec (.of R) := (pullbackSpecIso A R R).inv ≫ pullback.fst a₀ a₀
  let j₂ : Spec (.of D) ⟶ Spec (.of R) := (pullbackSpecIso A R R).inv ≫ pullback.snd a₀ a₀
  have hj₁ : j₁ = Spec.map (CommRingCat.ofHom (algebraMap R D)) := pullbackSpecIso_inv_fst' A R R
  have hj : j₁ ≫ a₀ = j₂ ≫ a₀ := by
    simp only [j₁, j₂, Category.assoc]
    exact (pullbackSpecIso A R R).inv ≫= pullback.condition
  let κs := (BigFppfOver.toScheme B S hS).map κ
  have hjκ : j₁ ≫ e.inv ≫ κs = j₂ ≫ e.inv ≫ κs := by
    simp only [κs, hκ, Iso.inv_hom_id_assoc]
    rw [← Category.assoc j₁, hj, Category.assoc]
  have hκw : κs ≫ B.inclusion.map V.hom = B.inclusion.map Vh.hom := by
    rw [← Over.w κ, Functor.map_comp]
    rfl
  -- `Spec D` as an object of the site, with its two projections to `V̂`
  let aD : Spec (.of D) ⟶ S := j₁ ≫ e.inv ≫ B.inclusion.map Vh.hom
  let Do := siteObject B S hS hD aD
  let p₁ : Do ⟶ Vh := Over.homMk (ObjectProperty.homMk (j₁ ≫ e.inv))
    (by apply ObjectProperty.hom_ext; rfl)
  have hp₂S : (j₂ ≫ e.inv) ≫ B.inclusion.map Vh.hom = aD := by
    simp only [aD, ← hκw, Category.assoc]
    rw [← Category.assoc e.inv, ← Category.assoc j₂, ← Category.assoc j₁, ← hjκ]
  let p₂ : Do ⟶ Vh := Over.homMk (ObjectProperty.homMk (j₂ ≫ e.inv))
    (by apply ObjectProperty.hom_ext; exact hp₂S)
  have hp₁ : (BigFppfOver.toScheme B S hS).map p₁ = j₁ ≫ e.inv := rfl
  have hp₂ : (BigFppfOver.toScheme B S hS).map p₂ = j₂ ≫ e.inv := rfl
  have hp₁κ : p₁ ≫ κ = p₂ ≫ κ := BigFppfOver.map_toScheme_injective B S hS (by
    show (BigFppfOver.toScheme B S hS).map (p₁ ≫ κ) = (BigFppfOver.toScheme B S hS).map (p₂ ≫ κ)
    rw [Functor.map_comp, Functor.map_comp, hp₁, hp₂, Category.assoc, Category.assoc]
    exact hjκ)
  have hpκs : (BigFppfOver.toScheme B S hS).map (p₁ ≫ κ) =
      j₁ ≫ a₀ ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv := by
    rw [Functor.map_comp, hp₁, hκ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  -- the points of `Spec D` lying over `T`
  have hKP : ∀ x : Spec (.of D),
      (j₁ ≫ a₀ ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv) x ∈
        ((BigFppfOver.toScheme B S hS).obj V).zeroLocus (I : Set A) ↔ J ≤ x.asIdeal := by
    intro x
    have h1 := Set.ext_iff.mp
      (((BigFppfOver.toScheme B S hS).obj V).isoSpec_inv_preimage_zeroLocus (I : Set A))
      (a₀ (j₁ x))
    rw [Set.mem_preimage] at h1
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]
    rw [hj₁]
    show (I : Set A) ⊆ Ideal.comap (algebraMap A R) (Ideal.comap (algebraMap R D) x.asIdeal) ↔ _
    rw [SetLike.coe_subset_coe, ← Ideal.map_le_iff_le_comap, ← Ideal.map_le_iff_le_comap]
  -- a site object over `Spec D` whose image misses `V(J)` maps into `U`
  have hlift : ∀ {Zo' : BigFppfOver B S hS} (z : Zo' ⟶ Do),
      (∀ y, ¬ J ≤ ((BigFppfOver.toScheme B S hS).map z y).asIdeal) →
      ∃ u : yoneda.obj Zo' ⟶ U.toFunctor, u ≫ U.ι = yoneda.map (z ≫ p₁ ≫ κ) := by
    intro Zo' z hzJ
    refine exists_lift_compl_of_range_subset B S hS V T (z ≫ p₁ ≫ κ) fun y hy => ?_
    obtain ⟨t, htT, hteq⟩ := hy
    have hmem := (hTI t).mp htT
    rw [hteq, Functor.map_comp, hpκs, Scheme.Hom.comp_apply, hKP] at hmem
    exact hzJ y hmem
  have hcd : yoneda.map p₁ ≫ h = yoneda.map p₂ ≫ h := by
    refine eq_of_eq_off_zeroLocus_of_eq_on_quotients_of_isProper B S hS hW
      (I.map (algebraMap A R)) hD aD _ _ ?_ ?_
      (isAlgebraicSpace_pullback B S hS (yoneda.map (p₁ ≫ κ)) f
        (isAlgebraicSpace_yoneda B S hS Do) hX' (isAlgebraicSpace_yoneda B S hS V))
      (pullback.fst (yoneda.map (p₁ ≫ κ)) f)
      (isProper_pullback_fst B S hS hX' (isAlgebraicSpace_yoneda B S hS V)
        (isAlgebraicSpace_yoneda B S hS Do) f (yoneda.map (p₁ ≫ κ)) hf) ?_ ?_
    · -- off `V(J)`
      intro Zo' z hzr
      obtain ⟨u, hu⟩ := hlift z fun y hy => hzr ⟨y, rfl⟩ ((PrimeSpectrum.mem_zeroLocus _ _).mpr hy)
      have e1 := hX'h (u ≫ sU) (yoneda.map (z ≫ p₁)) (by
        rw [Category.assoc, hsUf, hu, ← Functor.map_comp, Category.assoc])
      have e2 := hX'h (u ≫ sU) (yoneda.map (z ≫ p₂)) (by
        rw [Category.assoc, hsUf, hu, ← Functor.map_comp, Category.assoc, hp₁κ])
      simpa only [Functor.map_comp, Category.assoc] using e1.symm.trans e2
    · -- along `V(J)`
      rintro n Zo' z ⟨t, ht⟩
      have hzT : HasImageIn B S hS (yoneda.obj V) T Zo' ((z ≫ p₁) ≫ κ) := by
        rw [hasImageIn_iff_range_subset, yonedaEquiv_symm_eq_yoneda_map]
        rintro _ ⟨y, rfl⟩
        rw [hTI, pointsToScheme_pointsMap_yoneda, Category.assoc, Functor.map_comp, hpκs,
          Scheme.Hom.comp_apply, hKP, ht, Scheme.Hom.comp_apply]
        refine Ideal.IsPrime.le_of_pow_le (hP := PrimeSpectrum.isPrime _) (n := n) ?_
        show ((I.map (algebraMap A R)).map (algebraMap R D)) ^ n ≤ _
        rw [← Ideal.map_pow]
        intro a ha
        show Ideal.Quotient.mk _ a ∈ (t (pointsToScheme B S hS Zo' y)).asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact Ideal.zero_mem _
      have hzT' : HasImageIn B S hS (yoneda.obj V) T Zo' ((z ≫ p₂) ≫ κ) := by
        rw [Category.assoc, ← hp₁κ, ← Category.assoc]
        exact hzT
      apply yonedaEquiv.injective
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
        yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map,
        hh Zo' _ hzT, hh Zo' _ hzT']
      have heq : (z ≫ p₁) ≫ κ = (z ≫ p₂) ≫ κ := by
        rw [Category.assoc, hp₁κ, ← Category.assoc]
      rw [completion_app_congr B S hS V T ŵ hzT hzT' heq]
    · -- surjectivity of the base change of `f` off `V(J)`
      intro x hx
      obtain ⟨OD, hOD⟩ : ∃ OD : (Spec (.of D)).Opens,
          (OD : Set (Spec (.of D))) = (PrimeSpectrum.zeroLocus (J : Set D))ᶜ :=
        ⟨⟨_, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩, rfl⟩
      let DoU := openSiteObject B S hS Do OD
      let ιD : DoU ⟶ Do := openSiteObjectHom B S hS Do OD
      have hιD : (BigFppfOver.toScheme B S hS).map ιD = OD.ι := map_openSiteObjectHom B S hS Do OD
      obtain ⟨u, hu⟩ := hlift ιD fun y hy => by
        have hyO : OD.ι y ∈ (OD : Set (Spec (.of D))) := by
          rw [← Scheme.Opens.range_ι OD]
          exact ⟨y, rfl⟩
        rw [hOD] at hyO
        rw [hιD] at hy
        exact hyO ((PrimeSpectrum.mem_zeroLocus _ _).mpr hy)
      let L : yoneda.obj DoU ⟶ pullback (yoneda.map (p₁ ≫ κ)) f :=
        pullback.lift (yoneda.map ιD) (u ≫ sU) (by
          simp only [Category.assoc, hsUf, hu, Functor.map_comp])
      obtain ⟨x0, rfl⟩ : x ∈ Set.range OD.ι := by
        rw [Scheme.Opens.range_ι, hOD]
        exact hx
      obtain ⟨w0, hw0⟩ := surjective_pointsToScheme B S hS DoU x0
      refine ⟨pointsMap B S hS _ L w0, ?_⟩
      rw [← pointsMap_comp_apply, pullback.lift_fst, pointsToScheme_pointsMap_yoneda, hw0, hιD]
      rfl
    · -- agreement after the base change of `f`
      have e1 := hX'h (pullback.snd (yoneda.map (p₁ ≫ κ)) f)
        (pullback.fst (yoneda.map (p₁ ≫ κ)) f ≫ yoneda.map p₁) (by
          rw [← pullback.condition, Category.assoc, ← Functor.map_comp])
      have e2 := hX'h (pullback.snd (yoneda.map (p₁ ≫ κ)) f)
        (pullback.fst (yoneda.map (p₁ ≫ κ)) f ≫ yoneda.map p₂) (by
          rw [← pullback.condition, Category.assoc, ← Functor.map_comp, hp₁κ])
      simpa only [Category.assoc] using e1.symm.trans e2
  -- the factorization of `(z₁, z₂)` through `Spec D`
  have hzz : ((BigFppfOver.toScheme B S hS).map z₁ ≫ e.hom) ≫ a₀ =
      ((BigFppfOver.toScheme B S hS).map z₂ ≫ e.hom) ≫ a₀ := by
    have h1 := congrArg (BigFppfOver.toScheme B S hS).map hz
    rw [Functor.map_comp, Functor.map_comp, hκ] at h1
    simp only [Category.assoc] at h1 ⊢
    exact (cancel_mono _).mp h1
  let ls : (BigFppfOver.toScheme B S hS).obj Zo ⟶ Spec (.of D) :=
    pullback.lift _ _ hzz ≫ (pullbackSpecIso A R R).hom
  have hls₁ : ls ≫ j₁ = (BigFppfOver.toScheme B S hS).map z₁ ≫ e.hom := by
    simp only [ls, j₁, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
  have hls₂ : ls ≫ j₂ = (BigFppfOver.toScheme B S hS).map z₂ ≫ e.hom := by
    simp only [ls, j₂, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
  let l : Zo ⟶ Do := Over.homMk (ObjectProperty.homMk ls) (by
    apply ObjectProperty.hom_ext
    show ls ≫ j₁ ≫ e.inv ≫ B.inclusion.map Vh.hom = B.inclusion.map Zo.hom
    rw [reassoc_of% hls₁, e.hom_inv_id_assoc, ← Over.w z₁, Functor.map_comp]
    rfl)
  have hl₁ : l ≫ p₁ = z₁ := BigFppfOver.map_toScheme_injective B S hS (by
    show ls ≫ j₁ ≫ e.inv = (BigFppfOver.toScheme B S hS).map z₁
    rw [← Category.assoc, hls₁, Category.assoc, e.hom_inv_id, Category.comp_id])
  have hl₂ : l ≫ p₂ = z₂ := BigFppfOver.map_toScheme_injective B S hS (by
    show ls ≫ j₂ ≫ e.inv = (BigFppfOver.toScheme B S hS).map z₂
    rw [← Category.assoc, hls₂, Category.assoc, e.hom_inv_id, Category.comp_id])
  rw [← hl₁, ← hl₂, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcd]

/-! ### The spectrum of an adic completion as a member of the covering -/

/-- **`Spec Â ⟶ X` hits `V(I)`.** For an affine scheme `X` with ring `A` and an ideal `I ⊆ A`,
every point of the zero locus of `I` lies in the image of `Spec Â ⟶ Spec A ≅ X`, where `Â` is
the `I`-adic completion: a prime containing `I` is the inverse image of a prime of `A / I`, and
`A ⟶ A / I` factors through `Â`. -/
theorem zeroLocus_subset_range_specAdicCompletion (X : Scheme.{u}) [IsAffine X]
    (I : Ideal Γ(X, ⊤)) :
    X.zeroLocus (I : Set Γ(X, ⊤)) ⊆ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) ≫ X.isoSpec.inv) := by
  intro x hx
  have hy : X.isoSpec.hom x ∈
      PrimeSpectrum.zeroLocus ((RingHom.ker (Ideal.Quotient.mk (I ^ 1)) : Ideal Γ(X, ⊤)) :
        Set Γ(X, ⊤)) := by
    rw [Ideal.mk_ker, pow_one, ← X.isoSpec_image_zeroLocus]
    exact ⟨x, hx, rfl⟩
  rw [← _root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective] at hy
  obtain ⟨q, hq⟩ := hy
  let P : Spec (.of (AdicCompletion I Γ(X, ⊤))) :=
    PrimeSpectrum.comap (AdicCompletion.evalₐ I 1).toRingHom q
  refine ⟨P, ?_⟩
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤))))) P =
      X.isoSpec.hom x := by
    rw [← hq]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))
      (Ideal.comap (AdicCompletion.evalₐ I 1).toRingHom q.asIdeal) =
        Ideal.comap (Ideal.Quotient.mk (I ^ 1)) q.asIdeal
    rw [Ideal.comap_comap]
    congr 1
  rw [Scheme.Hom.comp_apply, h1, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- `Spec Â ⟶ Spec A ≅ X` is flat for the adic completion `Â` of the Noetherian ring `A` of an
affine scheme `X`. -/
theorem flat_specAdicCompletion (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) :
    AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) ≫ X.isoSpec.inv) := by
  have : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤))))) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  infer_instance

/-- `Spec Â ⟶ Spec A ≅ X` is quasi-compact. -/
theorem quasiCompact_specAdicCompletion (X : Scheme.{u}) [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    AlgebraicGeometry.QuasiCompact (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) ≫ X.isoSpec.inv) :=
  inferInstance

end Space

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.FibrewiseSmoothness
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.TowerStep
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.PartialIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ZeroSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic

/-!
# Flatness and smoothness of a tower of zero schemes, from one fibre

Let `f : P ⟶ S` be locally of finite presentation with `P` locally Noetherian, `I₀` a closed
subscheme of `P` flat over `S` near a point, and `G₁, …, G_c` sections of an invertible module.
Let `F` be the fibre of `f` over `s ∈ S`, presented by any cartesian square over
`Spec κ(s) ⟶ S`. If at a point `y ∈ F` every partial intersection
`(I₀ ∩ V(G₁, …, G_m))_s` is smooth of relative dimension `n - m` over `κ(s)`, then every
`I₀ ∩ V(G₁, …, G_m)` is flat over `S` near `y` ([Stacks, Tag 062Y] (3), one equation at a time)
and `I₀ ∩ V(G₁, …, G_c)` is smooth over `S` at `y` with fibre of dimension `n - c` there
([Stacks, Tag 01V9]). This is the fibrewise criterion of SGA 4, Exposé XI, Proposition 3.3.

Flatness near a point is recorded through an open immersion `Q ⟶ V(I)` whose image contains the
point, so that no open of the ambient scheme has to be chosen.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.pullbackGlobalSections_comp_ne_zero_of_isOpenImmersion`:
  a section nonzero on an integral scheme stays nonzero on a nonempty open.
* `AlgebraicGeometry.GoodNeighbourhood.exists_flat_zeroScheme_of_isPullback`: Tag 062Y (3) with
  the fibre presented by a cartesian square.
* `AlgebraicGeometry.GoodNeighbourhood.exists_flat_sup_zeroScheme_of_isPullback`: one more
  equation.
* `AlgebraicGeometry.GoodNeighbourhood.exists_flat_sup_partialIdeal_of_isPullback`: the tower.
* `AlgebraicGeometry.GoodNeighbourhood.exists_mem_smoothLocus_of_isPullback`: smoothness over
  `S` from flatness and smoothness of the fibre.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **A nonzero section on an integral scheme stays nonzero on a nonempty open.** If the pullback
of `g` along `b : Y ⟶ P` is nonzero and `Y` is integral, then so is its pullback along `a ≫ b` for
an open immersion `a` with nonempty source. -/
theorem pullbackGlobalSections_comp_ne_zero_of_isOpenImmersion {N Y P : Scheme.{u}} [IsIntegral Y]
    (a : N ⟶ Y) [IsOpenImmersion a] [Nonempty N] (b : Y ⟶ P) (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] (g : Γ(L, ⊤))
    (hb : pullbackGlobalSections b L g ≠ 0) : pullbackGlobalSections (a ≫ b) L g ≠ 0 := by
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback b).obj L) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback (h := ‹_›) b L
  rw [Ne, Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff]
  intro h
  have : IsDominant a := ⟨(a.isOpenEmbedding.isOpenMap.isOpen_range).dense
    (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant a := .of_isDominant a
  rw [Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker, a.ker_eq_bot] at h
  refine Stacks.ChernCap42.pullbackGlobalSections_ne_zero_of_isIso _ _ hb (𝟙 Y) ?_
  rw [Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker, Scheme.Hom.ker_eq_bot_of_isIso]
  exact h

/-- **The inverse image of a closed subscheme is a fibre product.** -/
theorem isPullback_comap_subschemeι {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι ((I.comapIso f).hom ≫ pullback.snd _ _) f I.subschemeι :=
  IsPullback.of_iso_pullback ⟨by
    rw [← I.comapIso_hom_fst f, Category.assoc, pullback.condition, Category.assoc]⟩
    (I.comapIso f) (I.comapIso_hom_fst f) rfl

/-- Base change of a cartesian square `K ⟶ J`, `X ⟶ Y` along `o : Q ⟶ J` is cartesian over `ι`. -/
private theorem isPullback_pullback_of_isPullback_subschemeι {X Y Q : Scheme.{u}}
    {J : Y.IdealSheafData} {ι : X ⟶ Y} {ρ : (J.comap ι).subscheme ⟶ J.subscheme}
    (hK : IsPullback (J.comap ι).subschemeι ρ ι J.subschemeι) (o : Q ⟶ J.subscheme) :
    IsPullback (pullback.snd ρ o) (pullback.fst ρ o ≫ (J.comap ι).subschemeι)
      (o ≫ J.subschemeι) ι :=
  (IsPullback.of_hasPullback ρ o).flip.paste_vert hK.flip

/-- Points of `K` and `Q` with the same image in `J` come from a common point of `K ×_J Q`. -/
private theorem exists_preimage_pullback_of_isPullback_subschemeι {X Y Q : Scheme.{u}}
    {J : Y.IdealSheafData} {ι : X ⟶ Y} {ρ : (J.comap ι).subscheme ⟶ J.subscheme}
    (hK : IsPullback (J.comap ι).subschemeι ρ ι J.subschemeι) (o : Q ⟶ J.subscheme)
    (y₀ : (J.comap ι).subscheme) (q₀ : Q)
    (h : J.subschemeι (o q₀) = ι ((J.comap ι).subschemeι y₀)) :
    ∃ w, pullback.fst ρ o w = y₀ ∧ pullback.snd ρ o w = q₀ := by
  refine Scheme.Pullback.exists_preimage_pullback y₀ q₀ ?_
  apply J.subschemeι.isClosedEmbedding.injective
  rw [h, ← Scheme.Hom.comp_apply, ← hK.w, Scheme.Hom.comp_apply]

/-- **Tag 062Y (3), with the fibre presented by a cartesian square.** Let `f : P ⟶ S` be flat and
locally of finite presentation, `g` a section of an invertible module vanishing at `z`, and let
`ι : F ⟶ P` present the fibre of `f` over `s = f z`. If on an integral scheme `Y₀` with an open
immersion into `F` through a point over `z` the pullback of `g` is nonzero, then the zero scheme of
`g` is flat over `S` on an open neighbourhood of `z`. -/
theorem exists_flat_zeroScheme_of_isPullback {P S : Scheme.{u}} (f : P ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] (g : Γ(L, ⊤)) (z : P)
    (hz : z ∈ (zeroScheme P L g).support) (s : S) (hzs : f z = s) {F : Scheme.{u}}
    (ι : F ⟶ P) (q : F ⟶ Spec (S.residueField s))
    (hF : IsPullback ι q f (S.fromSpecResidueField s)) {Y₀ : Scheme.{u}} [IsIntegral Y₀]
    (o : Y₀ ⟶ F) [IsOpenImmersion o] (y₀ : Y₀) (hy₀ : ι (o y₀) = z)
    (hg : pullbackGlobalSections (o ≫ ι) L g ≠ 0) :
    ∃ V : P.Opens, z ∈ V ∧ Flat (((zeroScheme P L g).comap V.ι).subschemeι ≫ V.ι ≫ f) := by
  subst hzs
  let e := hF.isoPullback
  let m : Y₀ ⟶ f.fiber (f z) := o ≫ e.hom
  have hm : m ≫ f.fiberι (f z) = o ≫ ι := by
    simp only [m]
    exact congrArg (o ≫ ·) hF.isoPullback_hom_fst
  have : IsOpenImmersion m :=
    @IsOpenImmersion.comp _ _ _ o e.hom _ (IsOpenImmersion.of_isIso e.hom)
  let U := m.opensRange
  let φ := IsOpenImmersion.isoOfRangeEq m U.ι
    (by rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])
  have : IsIntegral U.toScheme := IsIntegral.of_isIso φ.hom
  have hzU : f.asFiber z ∈ U := by
    refine ⟨y₀, ?_⟩
    apply (f.fiberHomeo (f z)).injective
    apply Subtype.ext
    rw [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber,
      ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₀]
  refine exists_flat_zeroScheme_of_fibre f L g z hz U hzU ?_
  have hU : U.ι ≫ f.fiberι (f z) = φ.inv ≫ o ≫ ι := by
    rw [← hm, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]
  rw [hU, Ne, Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker,
    Scheme.Hom.ker_comp_of_isIso, ← Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker]
  exact hg

/-- **One more equation.** Let `f : P ⟶ S` be locally of finite presentation with `P` locally
Noetherian, `ι : F ⟶ P` presenting the fibre over `s`, `y ∈ F`, and `J` a closed subscheme of `P`
flat over `S` on an open `Q` of `V(J)` containing `ι y`. If `V(J)_s` is smooth of relative
dimension `r + 1` near `y` and `V(J, g)_s` smooth of relative dimension `r` near `y`, then
`V(J, g)` is flat over `S` on an open containing `ι y` ([Stacks, Tag 062Y] (3)). -/
theorem exists_flat_sup_zeroScheme_of_isPullback {P S : Scheme.{u}} (f : P ⟶ S)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian P] (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (J : P.IdealSheafData) (g : Γ(L, ⊤)) (s : S) (r : ℕ) {F : Scheme.{u}}
    (ι : F ⟶ P) (q : F ⟶ Spec (S.residueField s))
    (hF : IsPullback ι q f (S.fromSpecResidueField s)) (y : F)
    {Q : Scheme.{u}} (o : Q ⟶ J.subscheme) [IsOpenImmersion o]
    (hyo : ι y ∈ Set.range (o ≫ J.subschemeι).base) [Flat (o ≫ J.subschemeι ≫ f)]
    (h₁ : SubschemeSmoothAt q (J.comap ι) (r + 1) y)
    (h₂ : SubschemeSmoothAt q ((J ⊔ zeroScheme P L g).comap ι) r y) :
    ∃ (Q' : Scheme.{u}) (o' : Q' ⟶ (J ⊔ zeroScheme P L g).subscheme), IsOpenImmersion o' ∧
      ι y ∈ Set.range (o' ≫ (J ⊔ zeroScheme P L g).subschemeι).base ∧
      Flat (o' ≫ (J ⊔ zeroScheme P L g).subschemeι ≫ f) := by
  set D := zeroScheme P L g with hD
  let h : Q ⟶ P := o ≫ J.subschemeι
  have hhf : h ≫ f = o ≫ J.subschemeι ≫ f := Category.assoc _ _ _
  have : Flat (h ≫ f) := by rw [hhf]; infer_instance
  have : LocallyOfFinitePresentation (h ≫ f) := by rw [hhf]; infer_instance
  have : SheafOfModules.IsInvertible Q.sheaf.obj Q.ringCatSheaf.property
      ((Scheme.Modules.pullback h).obj L) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback (h := ‹_›) h L
  have : SheafOfModules.IsInvertible F.sheaf.obj F.ringCatSheaf.property
      ((Scheme.Modules.pullback ι).obj L) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback (h := ‹_›) ι L
  set K := J.comap ι with hKdef
  let ρ : K.subscheme ⟶ J.subscheme := (J.comapIso ι).hom ≫ pullback.snd _ _
  have hK : IsPullback K.subschemeι ρ ι J.subschemeι := isPullback_comap_subschemeι J ι
  have hFq : IsPullback (pullback.snd ρ o) (pullback.fst ρ o ≫ K.subschemeι) h ι :=
    isPullback_pullback_of_isPullback_subschemeι hK o
  have hFq' : IsPullback (pullback.snd ρ o) ((pullback.fst ρ o ≫ K.subschemeι) ≫ q) (h ≫ f)
      (S.fromSpecResidueField s) := hFq.paste_vert hF
  have h₂' : SubschemeSmoothAt q (K ⊔ zeroScheme F ((Scheme.Modules.pullback ι).obj L)
      (pullbackGlobalSections ι L g)) r y := by
    have hzp : zeroScheme F ((Scheme.Modules.pullback ι).obj L) (pullbackGlobalSections ι L g) =
        D.comap ι := Stacks.Divisors.zeroScheme_pullback ι L g
    rw [hzp, hKdef, ← (Scheme.IdealSheafData.map_gc ι).l_sup]
    exact h₂
  have : IsNormal (Spec (S.residueField s)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  obtain ⟨y₀, U₀, hy₀, hy₀U, hU₀, hne⟩ :=
    exists_isIntegral_ne_zero_of_subschemeSmoothAt q K _ _ r y h₁ h₂'
  have hne' : pullbackGlobalSections (U₀.ι ≫ K.subschemeι ≫ ι) L g ≠ 0 := by
    rw [← Category.assoc, Ne, Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff]
    exact hne
  obtain ⟨q₀, hq₀⟩ := hyo
  have hq₀' : J.subschemeι (o q₀) = ι y := hq₀
  obtain ⟨w, hw₁, hw₂⟩ :=
    exists_preimage_pullback_of_isPullback_subschemeι hK o y₀ q₀ (hq₀'.trans (congrArg ι hy₀.symm))
  let N := (pullback.fst ρ o) ⁻¹ᵁ U₀
  have hwN : w ∈ N := by
    change pullback.fst ρ o w ∈ U₀
    rw [hw₁]; exact hy₀U
  have : Nonempty N := ⟨⟨w, hwN⟩⟩
  have : IsIntegral U₀.toScheme := hU₀
  have : IsIntegral N.toScheme := isIntegral_of_isOpenImmersion (pullback.fst ρ o ∣_ U₀)
  have hyD : ι y ∈ (D.support : Set P) := by
    obtain ⟨y₂, hy₂, -⟩ := h₂
    have hy : y ∈ (((J ⊔ D).comap ι).support : Set F) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y₂, hy₂⟩
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_sup] at hy
    exact hy.2
  have hzD : q₀ ∈ (zeroScheme Q ((Scheme.Modules.pullback h).obj L)
      (pullbackGlobalSections h L g)).support := by
    have hzp : zeroScheme Q ((Scheme.Modules.pullback h).obj L) (pullbackGlobalSections h L g) =
        D.comap h := Stacks.Divisors.zeroScheme_pullback h L g
    rw [hzp, Scheme.IdealSheafData.support_comap]
    change h q₀ ∈ (D.support : Set P)
    exact hq₀'.symm ▸ hyD
  have hfs : (h ≫ f) q₀ = s := by
    have e1 : (h ≫ f) q₀ = f (ι y) := by
      rw [Scheme.Hom.comp_apply]; exact congrArg f hq₀'
    rw [e1, ← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  have hgN : pullbackGlobalSections (N.ι ≫ pullback.snd ρ o) ((Scheme.Modules.pullback h).obj L)
      (pullbackGlobalSections h L g) ≠ 0 := by
    rw [Ne, ← Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff]
    have e : (N.ι ≫ pullback.snd ρ o) ≫ h =
        (pullback.fst ρ o ∣_ U₀) ≫ U₀.ι ≫ K.subschemeι ≫ ι := by
      rw [Category.assoc, hFq.w, ← Category.assoc, ← Category.assoc, ← morphismRestrict_ι,
        Category.assoc, Category.assoc]
    rw [e]
    exact pullbackGlobalSections_comp_ne_zero_of_isOpenImmersion _ _ L g hne'
  obtain ⟨V, hq₀V, hVflat⟩ := exists_flat_zeroScheme_of_isPullback (h ≫ f)
    ((Scheme.Modules.pullback h).obj L) (pullbackGlobalSections h L g) q₀ hzD s hfs
    (pullback.snd ρ o) ((pullback.fst ρ o ≫ K.subschemeι) ≫ q) hFq' N.ι ⟨w, hwN⟩
    (by change pullback.snd ρ o w = q₀; exact hw₂) hgN
  have hzp : zeroScheme Q ((Scheme.Modules.pullback h).obj L) (pullbackGlobalSections h L g) =
      D.comap h := Stacks.Divisors.zeroScheme_pullback h L g
  rw [hzp] at hVflat
  have hcomap : (D.comap h).comap V.ι = (D.comap J.subschemeι).comap (V.ι ≫ o) := by
    simp only [h, Scheme.IdealSheafData.comap_comp]
  rw [hcomap] at hVflat
  set D' := D.comap J.subschemeι with hD'
  let o₁ : V.toScheme ⟶ J.subscheme := V.ι ≫ o
  obtain ⟨e', he'⟩ := Stacks.ChernCap42.exists_iso_comap_sup J D J.subschemeι (Iso.refl _)
    (Category.id_comp _)
  let o' := (D'.comapIso o₁).hom ≫ pullback.snd o₁ D'.subschemeι ≫ e'.hom
  have : IsOpenImmersion o' :=
    @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _)
      (@IsOpenImmersion.comp _ _ _ _ _ inferInstance (IsOpenImmersion.of_isIso _))
  have key : o' ≫ (J ⊔ D).subschemeι =
      (D'.comapIso o₁).hom ≫ pullback.fst o₁ D'.subschemeι ≫ o₁ ≫ J.subschemeι := by
    simp only [o', Category.assoc, he']
    rw [← pullback.condition_assoc]
  refine ⟨(D'.comap o₁).subscheme, o', inferInstance, ?_, ?_⟩
  · have hoD : o₁ ⟨q₀, hq₀V⟩ ∈ (D'.support : Set J.subscheme) := by
      rw [hD', Scheme.IdealSheafData.support_comap]
      change J.subschemeι (o q₀) ∈ (D.support : Set P)
      rw [hq₀']; exact hyD
    rw [← Scheme.IdealSheafData.range_subschemeι] at hoD
    obtain ⟨a, ha⟩ := hoD
    obtain ⟨b, hb₁, hb₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ ha.symm
    refine ⟨(D'.comapIso o₁).inv b, ?_⟩
    show (o' ≫ (J ⊔ D).subschemeι) ((D'.comapIso o₁).inv b) = ι y
    rw [key, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, Scheme.Hom.comp_apply, hb₁]
    exact hq₀'
  · have e : o' ≫ (J ⊔ D).subschemeι ≫ f = (D'.comap o₁).subschemeι ≫ V.ι ≫ h ≫ f := by
      rw [← Category.assoc, key]
      simp only [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc, o₁, h]
    rw [e]
    exact hVflat

/-- **Smoothness from flatness and the fibre.** If `V(J)` is flat over `S` on an open `Q`
containing `ι y`, and `V(J)_s` is smooth of relative dimension `n` near `y`, then the point of
`V(J)` over `ι y` is a point of smoothness of `V(J) ⟶ S`, with fibre of dimension `n` there
([Stacks, Tag 01V9], via [Stacks, Tag 02V4]). -/
theorem exists_mem_smoothLocus_of_isPullback {P S : Scheme.{u}} (f : P ⟶ S)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian P] (J : P.IdealSheafData) (s : S)
    {F : Scheme.{u}} (ι : F ⟶ P) (q : F ⟶ Spec (S.residueField s))
    (hF : IsPullback ι q f (S.fromSpecResidueField s)) (y : F) (n : ℕ)
    {Q : Scheme.{u}} (o : Q ⟶ J.subscheme) [IsOpenImmersion o]
    (hyo : ι y ∈ Set.range (o ≫ J.subschemeι).base) [Flat (o ≫ J.subschemeι ≫ f)]
    (hsm : SubschemeSmoothAt q (J.comap ι) n y) :
    ∃ z : J.subscheme, J.subschemeι z = ι y ∧ z ∈ (J.subschemeι ≫ f).smoothLocus ∧
      topologicalKrullDimAt ((J.subschemeι ≫ f).fiber ((J.subschemeι ≫ f) z))
        ((J.subschemeι ≫ f).asFiber z) = (n : WithBot ℕ∞) := by
  set K := J.comap ι with hKdef
  obtain ⟨y₁, hy₁, U₁, hyU₁, hsm₁⟩ := hsm
  let ρ : K.subscheme ⟶ J.subscheme := (J.comapIso ι).hom ≫ pullback.snd _ _
  have hK : IsPullback K.subschemeι ρ ι J.subschemeι := isPullback_comap_subschemeι J ι
  have hFq := isPullback_pullback_of_isPullback_subschemeι hK o
  have hFq' : IsPullback (pullback.snd ρ o) (pullback.fst ρ o ≫ K.subschemeι ≫ q)
      (o ≫ J.subschemeι ≫ f) (S.fromSpecResidueField s) := by
    simpa only [Category.assoc] using hFq.paste_vert hF
  obtain ⟨q₀, hq₀⟩ := hyo
  have hq₀' : J.subschemeι (o q₀) = ι y := hq₀
  obtain ⟨w, hw₁, hw₂⟩ :=
    exists_preimage_pullback_of_isPullback_subschemeι hK o y₁ q₀ (hq₀'.trans (congrArg ι hy₁.symm))
  let g' := pullback.fst ρ o ≫ K.subschemeι ≫ q
  have : LocallyOfFinitePresentation g' := MorphismProperty.of_isPullback hFq' inferInstance
  let N := (pullback.fst ρ o) ⁻¹ᵁ U₁
  have hwN : w ∈ N := by
    change pullback.fst ρ o w ∈ U₁
    rw [hw₁]; exact hyU₁
  have hNg : N.ι ≫ g' = (pullback.fst ρ o ∣_ U₁) ≫ U₁.ι ≫ K.subschemeι ≫ q := by
    rw [← morphismRestrict_ι_assoc]
  have : SmoothOfRelativeDimension n (N.ι ≫ g') := by
    rw [hNg]
    have h' : SmoothOfRelativeDimension (0 + n)
        ((pullback.fst ρ o ∣_ U₁) ≫ U₁.ι ≫ K.subschemeι ≫ q) := inferInstance
    simpa only [zero_add] using h'
  have hwsm : w ∈ g'.smoothLocus := by
    have h' : (N.ι ≫ g').smoothLocus = ⊤ :=
      Scheme.Hom.smoothLocus_eq_top_iff.2 (SmoothOfRelativeDimension.smooth n _)
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h'
    have h'' : (⟨w, hwN⟩ : N.toScheme) ∈ N.ι ⁻¹ᵁ g'.smoothLocus := h' ▸ trivial
    exact h''
  rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hFq' (Or.inl inferInstance)] at hwsm
  have hwsm' : q₀ ∈ (o ≫ J.subschemeι ≫ f).smoothLocus := by
    have h' : pullback.snd ρ o w ∈ (o ≫ J.subschemeι ≫ f).smoothLocus := hwsm
    rwa [hw₂] at h'
  refine ⟨o q₀, hq₀', ?_, ?_⟩
  · rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hwsm'
  · calc topologicalKrullDimAt ((J.subschemeι ≫ f).fiber ((J.subschemeι ≫ f) (o q₀)))
          ((J.subschemeι ≫ f).asFiber (o q₀))
        = topologicalKrullDimAt ((o ≫ J.subschemeι ≫ f).fiber ((o ≫ J.subschemeι ≫ f) q₀))
            ((o ≫ J.subschemeι ≫ f).asFiber q₀) :=
          (fiberDimensionAt_comp_openImmersion o (J.subschemeι ≫ f) q₀).symm
      _ = topologicalKrullDimAt ((o ≫ J.subschemeι ≫ f).fiber
            ((o ≫ J.subschemeι ≫ f) (pullback.snd ρ o w)))
            ((o ≫ J.subschemeι ≫ f).asFiber (pullback.snd ρ o w)) := by rw [hw₂]
      _ = topologicalKrullDimAt (g'.fiber (g' w)) (g'.asFiber w) :=
          (topologicalKrullDimAt_fiber_eq_of_isPullback hFq' w).symm
      _ = topologicalKrullDimAt ((N.ι ≫ g').fiber ((N.ι ≫ g') ⟨w, hwN⟩))
            ((N.ι ≫ g').asFiber ⟨w, hwN⟩) :=
          (fiberDimensionAt_comp_openImmersion N.ι g' ⟨w, hwN⟩).symm
      _ = (n : WithBot ℕ∞) := fiberDimensionAt_eq_of_smoothOfRelativeDimension _ n _

/-- **The tower** ([Stacks, Tag 062Y] (3) iterated). If `V(I₀)` is flat over `S` near `ι y` and
every `(I₀ ∩ V(G₁, …, G_m))_s`, `m ≤ c`, is smooth of relative dimension `n - m` near `y`, then
every `I₀ ∩ V(G₁, …, G_m)` is flat over `S` on an open containing `ι y`. -/
theorem exists_flat_sup_partialIdeal_of_isPullback {P S : Scheme.{u}} (f : P ⟶ S)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian P] (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (I₀ : P.IdealSheafData) {c : ℕ} (G : Fin c → Γ(L, ⊤)) (s : S) {F : Scheme.{u}}
    (ι : F ⟶ P) (q : F ⟶ Spec (S.residueField s))
    (hF : IsPullback ι q f (S.fromSpecResidueField s)) (y : F) (n : ℕ) (hcn : c ≤ n)
    (h₀ : ∃ (Q : Scheme.{u}) (o : Q ⟶ I₀.subscheme), IsOpenImmersion o ∧
      ι y ∈ Set.range (o ≫ I₀.subschemeι).base ∧ Flat (o ≫ I₀.subschemeι ≫ f))
    (hfib : ∀ m ≤ c, SubschemeSmoothAt q ((I₀ ⊔ partialIdeal L G m).comap ι) (n - m) y) :
    ∀ m ≤ c, ∃ (Q : Scheme.{u}) (o : Q ⟶ (I₀ ⊔ partialIdeal L G m).subscheme),
      IsOpenImmersion o ∧ ι y ∈ Set.range (o ≫ (I₀ ⊔ partialIdeal L G m).subschemeι).base ∧
      Flat (o ≫ (I₀ ⊔ partialIdeal L G m).subschemeι ≫ f) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [partialIdeal_zero, sup_bot_eq]
    exact h₀
  | succ m ih =>
    intro hm
    obtain ⟨Q, o, ho, hyo, hfl⟩ := ih (Nat.le_of_succ_le hm)
    have hmc : m < c := hm
    have h₁ := hfib m (Nat.le_of_succ_le hm)
    have h₂ := hfib (m + 1) hm
    have hnm : n - m = n - (m + 1) + 1 := by omega
    rw [hnm] at h₁
    rw [partialIdeal_succ L G m hmc, ← sup_assoc] at h₂ ⊢
    exact exists_flat_sup_zeroScheme_of_isPullback f L _ (G ⟨m, hmc⟩) s _ ι q hF y o hyo h₁ h₂

end AlgebraicGeometry.GoodNeighbourhood

end

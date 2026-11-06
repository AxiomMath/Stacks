module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianColimitPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionNeighbourhoodCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# A locally Noetherian formal algebraic space as a colimit of thickenings

This file proves **Stacks 0GHM**: a locally Noetherian formal algebraic space `X` over `S` is
the colimit `X = colim X_n` of a system `X_0 ⟶ X_1 ⟶ X_2 ⟶ ⋯` of finite-order thickenings of
locally Noetherian algebraic spaces over `S`, where `X_0 = X_red` and `X_n` is the `n`th
infinitesimal neighbourhood of `X_0` in `X_m` for every `m ≥ n`. The stages are indexed from
zero, so the stage `n` here is the source's `X_{n+1}`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_finiteOrderThickening_presentation_of_isLocallyNoetherian`:
  **Stacks 0GHM**.
* `AlgebraicGeometry.FormalSpace.exists_chain_of_isNoetherian`: the input of the proof from the
  Noetherian affine case: a Noetherian affine formal algebraic space is the colimit of a chain of
  Noetherian affine schemes along closed immersions, with reduced first stage, the `n`th stage
  cut out of the `m`th by the `(n + 1)`st power of the ideal of the first, whose stages are
  representable thickenings covering it locally.
* `AlgebraicGeometry.FormalSpace.hasEtaleLocalPropertyULift_isLocallyNoetherian_of_etale_charts`:
  an algebraic space with a jointly locally surjective family of étale charts by locally
  Noetherian schemes is locally Noetherian.

## Implementation notes

The proof is the source's. With `i : X_red ⟶ X` the reduction of `X` (Stacks 0AIN), `X_n ⊂ X`
is the subfunctor of the sections `ξ` over `T` whose ideal sheaf `I_ξ` of `X_red ×_X T ⊂ T` has
vanishing `(n + 1)`st power (`AlgebraicGeometry.FormalSpace.neighbourhood`). Its base change
along a scheme `T` is the closed subscheme `V(I_ξ ^ (n + 1))` of `T`, which gives representability,
the thickening properties and the infinitesimal-neighbourhood clause directly, with no reduction
to the affine case; and `X_0` is the image of `i`
(`AlgebraicGeometry.FormalSpace.ReductionNeighbourhood`).

What is checked étale locally on `X`, as in the source, is that each `X_n` is an algebraic space
and that `X` is the colimit of the `X_n`. Over a member `X_j = Spf A_j` of an atlas by Noetherian
affine formal algebraic spaces the reduction of `X` pulls back to the reduction of `X_j`
(`AlgebraicGeometry.FormalSpace.exists_isPullback_of_isReduction_of_etale`), so `X_n` pulls back
to the `n`th neighbourhood of `X_{j,red}` in `X_j`, which is the stage `Spec (A_j ⧸ 𝔞_j ^ (n + 1))`
of the presentation of the Noetherian affine case
(`AlgebraicGeometry.FormalSpace.exists_finiteOrderThickening_presentation_formalSpectrum`,
`AlgebraicGeometry.FormalSpace.neighbourhood_eq_range_of_chain`). These stages form an étale
covering of `X_n` by Noetherian affine schemes, which makes `X_n` a locally Noetherian algebraic
space (`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_of_reduced_etale_cover`), and every
section of `X` lies locally in one of them, which makes `X` the colimit
(`AlgebraicGeometry.FormalSpace.isIso_colimitDesc_neighbourhoodCocone`).

That `X_n ⟶ X_m` is a finite-order thickening is stated as: it is representable, and every
represented base change is an `m`th-order thickening of schemes; the order is uniform, as Stacks
04EX asks. The infinitesimal-neighbourhood clause is stated, as in the Noetherian affine case, as
the equality of ideal sheaves `I(X_0) ^ (n + 1) = I(X_n)` on every represented base change of
`X_m`. That `X_0` is the reduction is `AlgebraicGeometry.FormalSpace.IsReduction` for the colimit
leg at `0`.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] sheaf_hasColimits

/-! ### Stages of a chain presentation -/

/-- A morphism of fppf sheaves which is representable relative to the sheafified Yoneda embedding,
with every represented base change a thickening, is a representable thickening relative to the
universe-lifted Yoneda embedding of presheaves. -/
theorem isRepresentableThickeningULift_of_relative_sheafifiedYoneda {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y}
    (h : MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) f) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS f.hom := by
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  have : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    isThickening_isStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let ε : Sheaf.sheafifiedYoneda JT ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  apply MorphismProperty.relative.of_exists
  intro a g
  let g' : (Sheaf.sheafifiedYoneda JT).obj a ⟶ Y := ⟨(ε.app a).hom ≫ g⟩
  obtain ⟨b, snd, fst, sq⟩ := h.rep g'
  refine ⟨b, (ε.app b).inv ≫ fst.hom, snd, ?_, h.property g' fst snd sq⟩
  exact (sq.map (sheafToPresheaf JT (Type (u + 1)))).of_iso
    (ε.app b) (Iso.refl _) (ε.app a) (Iso.refl _)
    (by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom, Category.comp_id]
      rfl)
    (ε.hom.naturality snd) (by simp) (by simp [g'])

/-- **The stages of a colimit of a chain of affine schemes along thickenings are representable
thickenings.** This is Stacks 0AI9 for a chain indexed by `ℕ`, read relative to the
universe-lifted Yoneda embedding. -/
theorem isRepresentableThickeningULift_colimitι_of_chain (E : ℕ ⥤ BigAffineFppf B S hS)
    (hE : ∀ ⦃n m : ℕ⦄ (f : n ⟶ m),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map f)))
    {Y : FppfSheaf B S hS}
    (e : colimit (E ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ Y) (n : ℕ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (colimit.ι (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) n ≫ e.hom).hom := by
  let L := ULift.{u + 1} ℕ
  let eOrder : ℕ ≃o L := { toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl }
  let eL : ℕ ≌ L := eOrder.equivalence
  have : IsDirected L (· ≤ ·) := ⟨fun a b ↦
    ⟨ULift.up (max a.down b.down), (le_max_left a.down b.down : _),
      (le_max_right a.down b.down : _)⟩⟩
  let G := E ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let e' : colimit ((eL.inverse ⋙ E) ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ Y :=
    Functor.Final.colimitIso eL.inverse G ≪≫ e
  have h := isThickening_colimitι B S hS (eL.inverse ⋙ E)
    (fun _ _ f ↦ hE (eL.inverse.map f)) Y e' (ULift.up n)
  have heq : colimit.ι ((eL.inverse ⋙ E) ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (ULift.up n) ≫ e'.hom =
        colimit.ι G n ≫ e.hom := by
    show colimit.ι (eL.inverse ⋙ G) (ULift.up n) ≫
      (Functor.Final.colimitIso eL.inverse G).hom ≫ e.hom = _
    rw [Functor.Final.ι_colimitIso_hom_assoc]
    rfl
  rw [heq] at h
  exact isRepresentableThickeningULift_of_relative_sheafifiedYoneda h

/-- **The Noetherian affine case, in the form the proof of Stacks 0GHM uses.** A Noetherian
affine formal algebraic space `Y` carries stages `ρ_n : E_n ⟶ Y` along a chain of Noetherian
affine objects of the site and closed immersions `E_0 ⟶ E_1 ⟶ ⋯`, with `E_0` reduced and `E_n`
cut out of `E_m` by the `(n + 1)`st power of the ideal of `E_0`, each stage a representable
thickening, and the stages covering `Y` locally. -/
theorem exists_chain_of_isNoetherian (Y : FppfSheaf B S hS) (hY : IsNoetherian B S hS Y) :
    ∃ (E : ℕ ⥤ BigFppfOver B S hS) (ρ : ∀ n, uliftYoneda.{u + 1}.obj (E.obj n) ⟶ Y.obj)
      (hρ : ∀ n, Space.IsRepresentableThickeningULift.{u + 1} B S hS (ρ n)),
      (∀ n, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj n))) ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj (E.obj 0)) ∧
      (∀ n, AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (E.obj n))) ∧
      (∀ (n m : ℕ) (h : n ≤ m), uliftYoneda.{u + 1}.map (E.map (homOfLE h)) ≫ ρ m = ρ n) ∧
      (∀ (n m : ℕ) (h : n ≤ m), AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE h)))) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE (Nat.zero_le m)))).ker ^ (n + 1) =
          ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE h))).ker) ∧
      (∀ (T : BigFppfOver B S hS) (y : Y.obj.obj (op T)),
        (⨆ m, (Subfunctor.range (ρ m)).sieveOfSection y) ∈ BigFppfOver.topology B S hS T) := by
  obtain ⟨-, A, _, _, _, _, ⟨-, ⟨P⟩⟩, hnoeth, ⟨⟨I, -, hI⟩, -⟩⟩ := hY
  have : IsNoetherianRing A := hnoeth
  let JT := BigFppfOver.topology B S hS
  let D := P.quotientSystem
  obtain ⟨E₀, hred, hnoethE, hthick, hkerE, ⟨eF⟩⟩ :=
    exists_finiteOrderThickening_presentation_formalSpectrum hI D
  let G := E₀ ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda JT
  let e : colimit G ≅ Y := (P.formalSpectrumIso ≪≫ eF).symm
  let E := E₀ ⋙ BigAffineFppf.inclusion B S hS
  let ι (n : ℕ) := (sheafifiedYonedaObjIso B S hS (E.obj n)).hom
  let ρ (n : ℕ) : uliftYoneda.{u + 1}.obj (E.obj n) ⟶ Y.obj := ι n ≫ (colimit.ι G n ≫ e.hom).hom
  have : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}
        (C := BigFppfOver B S hS)) |>.RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1})
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).respectsIso
  have hρ (n : ℕ) : Space.IsRepresentableThickeningULift.{u + 1} B S hS (ρ n) :=
    MorphismProperty.RespectsIso.precomp _ (ι n) _
      (isRepresentableThickeningULift_colimitι_of_chain E₀ (fun _ _ f ↦ (hthick f).isThickening)
        e n)
  have hmono : ∀ (n m : ℕ) (f : n ⟶ m), Mono (G.map f) := by
    intro n m f
    have : AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (E.map f)) := (hthick f).1
    have : (BigFppfOver.toScheme B S hS).Faithful := by
      dsimp [BigFppfOver.toScheme]
      infer_instance
    have : Mono (E.map f) := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
    have : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda JT) := by
      dsimp [Sheaf.sheafifiedYoneda]
      infer_instance
    show Mono ((Sheaf.sheafifiedYoneda JT).map (E.map f))
    infer_instance
  refine ⟨E, ρ, hρ, fun n ↦ (E₀.obj n).property, hred, hnoethE, ?_, fun n m h ↦ (hthick _).1,
    hkerE, ?_⟩
  · intro n m h
    show uliftYoneda.{u + 1}.map (E.map (homOfLE h)) ≫ ι m ≫ (colimit.ι G m ≫ e.hom).hom =
      ι n ≫ (colimit.ι G n ≫ e.hom).hom
    rw [← Category.assoc, sheafifiedYonedaObjIso_naturality B S hS (E.map (homOfLE h)),
      Category.assoc, ← colimit.w G (homOfLE h)]
    rfl
  · intro T y
    apply mem_topology_of_forall_isAffine
    intro U g hU
    obtain ⟨m, z, hz⟩ := exists_colimitι_app_eq_of_isAffine G hmono hU
      (e.inv.hom.app (op U) (Y.obj.map g.op y))
    refine (sieve_arrows_iSup_iff _ g).mpr ⟨m, ?_⟩
    refine ⟨(sheafifiedYonedaObjIso B S hS (E.obj m)).inv.app (op U) z, ?_⟩
    show (colimit.ι G m ≫ e.hom).hom.app (op U)
      ((ι m).app (op U) ((sheafifiedYonedaObjIso B S hS (E.obj m)).inv.app (op U) z)) = _
    rw [show (ι m).app (op U) ((sheafifiedYonedaObjIso B S hS (E.obj m)).inv.app (op U) z) = z
      from ConcreteCategory.congr_hom
        (congr_app (sheafifiedYonedaObjIso B S hS (E.obj m)).inv_hom_id (op U)) z]
    show e.hom.hom.app (op U) ((colimit.ι G m).hom.app (op U) z) = _
    rw [hz]
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun t ↦ t.hom) e.inv_hom_id) (op U)) _

/-! ### Local Noetherianity from étale charts -/

/-- **An algebraic space with a jointly locally surjective family of étale charts by locally
Noetherian schemes is locally Noetherian.** Any scheme atlas `W` is: its fibre products with the
charts are étale over the charts, hence locally Noetherian, and they form an étale covering of
`W`. -/
theorem hasEtaleLocalPropertyULift_isLocallyNoetherian_of_etale_charts {R : FppfSheaf B S hS}
    (halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj) {I : Type (u + 1)}
    (U : I → BigFppfOver B S hS)
    (hU : ∀ j, AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (U j)))
    (c : ∀ j, uliftYoneda.{u + 1}.obj (U j) ⟶ R.obj)
    (hc : ∀ j, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (c j))
    (hcov : ∀ (T : BigFppfOver B S hS) (x : R.obj.obj (op T)),
      (⨆ j, Presheaf.imageSieve (c j) x) ∈ BigFppfOver.topology B S hS T) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS R.obj
      (fun T : Scheme.{u} ↦ AlgebraicGeometry.IsLocallyNoetherian T) := by
  classical
  obtain ⟨W, q, hqs, hqe⟩ := halg.exists_atlas
  refine ⟨W, q, hqs, hqe, ?_⟩
  let G := BigFppfOver.toScheme B S hS
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let P (j : I) : BigFppfOver B S hS := (hc j).rep.pullback q
  let s (j : I) : P j ⟶ W := (hc j).rep.snd q
  let h (j : I) : P j ⟶ U j := Y.preimage ((hc j).rep.fst q)
  have hs (j : I) : Etale (G.map (s j)) := (hc j).property q _ _ ((hc j).rep.isPullback q)
  have hh (j : I) : Etale (G.map (h j)) := by
    refine hqe.property (c j) (Y.map (s j)) (h j) ?_
    rw [Y.map_preimage]
    exact ((hc j).rep.isPullback q).flip
  have hP (j : I) : AlgebraicGeometry.IsLocallyNoetherian (G.obj (P j)) := by
    have := hU j
    have := hh j
    exact LocallyOfFiniteType.isLocallyNoetherian (G.map (h j))
  have hpoint : ∀ w : W.left.obj, ∃ j, w ∈ Set.range (s j).left.hom := by
    have hmem := hcov W (uliftYonedaEquiv.{u + 1} q)
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hmem
    have hEF := B.isFppfCovering_of_isCovering hE
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
    intro w
    obtain ⟨i, y, hy⟩ := hEF.1 w
    let T' : BigFppfOver B S hS := Over.mk (E.f i ≫ W.hom)
    let b : T' ⟶ W := Over.homMk (E.f i)
    have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨i⟩)
    change (⨆ j, Presheaf.imageSieve (c j) (uliftYonedaEquiv.{u + 1} q)) b at hb
    obtain ⟨j, z, hz⟩ := (sieve_arrows_iSup_iff _ b).mp hb
    have hw : uliftYonedaEquiv.{u + 1}.symm z ≫ c j = Y.map b ≫ q := by
      apply uliftYonedaEquiv.injective
      rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} q b.op)
    let a : T' ⟶ P j := Y.preimage (((hc j).rep.isPullback q).lift _ _ hw)
    have hab : a ≫ s j = b := by
      apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage]
      exact ((hc j).rep.isPullback q).lift_snd _ _ _
    refine ⟨j, a.left.hom y, ?_⟩
    rwa [← Scheme.Hom.comp_apply, ← show (a ≫ s j).left.hom =
      a.left.hom ≫ (s j).left.hom from rfl, hab]
  choose idx hidx using hpoint
  refine ObjectProperty.IsLocal.of_presieve (K := Scheme.etalePrecoverage)
    (R := Presieve.ofArrows (fun w ↦ G.obj (P (idx w))) (fun w ↦ G.map (s (idx w)))) ?_ ?_
  · exact (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun w ↦ ⟨w, hidx w⟩, fun w ↦ hs (idx w)⟩
  · rintro _ _ ⟨w⟩
    exact hP (idx w)

/-! ### Stacks 0GHM -/

/-- **Stacks 0GHM.** Let `X` be a locally Noetherian formal algebraic space over `S`. Then
`X = colim X_n` for a system `X_0 ⟶ X_1 ⟶ X_2 ⟶ ⋯` of finite-order thickenings of locally
Noetherian algebraic spaces over `S`, where `X_0 = X_red` and `X_n` is the `n`th infinitesimal
neighbourhood of `X_0` in `X_m` for all `m ≥ n`.

The stages are indexed from zero, so the stage `n` is the source's `X_{n+1}`. In detail: every
`X_n` is an algebraic space whose étale atlases are locally Noetherian; every transition morphism
`X_n ⟶ X_m` is representable and an `m`th-order thickening on every represented base change; on
every represented base change along a section of `X_m`, the ideal sheaf of `X_n` is the
`(n + 1)`st power of the ideal sheaf of `X_0`; and `X` is the colimit of the `X_n`, its colimit
leg at `0` exhibiting `X_0` as the reduction of `X`. -/
@[stacks 0GHM]
theorem exists_finiteOrderThickening_presentation_of_isLocallyNoetherian
    (X : FppfSheaf B S hS) (hX : IsLocallyNoetherian B S hS X) :
    ∃ E : ℕ ⥤ FppfSheaf B S hS,
      (∀ n, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj n).obj) ∧
      (∀ n, Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (E.obj n).obj
        (fun T : Scheme.{u} ↦ AlgebraicGeometry.IsLocallyNoetherian T)) ∧
      (∀ ⦃n m : ℕ⦄ (f : n ⟶ m), Space.HasSchemePropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Stacks.Thickenings.IsNthOrderThickening m k) (E.map f).hom) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m) {a b c : BigFppfOver B S hS}
        (g : uliftYoneda.{u + 1}.obj a ⟶ (E.obj m).obj)
        {fst₀ : uliftYoneda.{u + 1}.obj b ⟶ (E.obj 0).obj} {snd₀ : b ⟶ a}
        (_ : IsPullback fst₀ (uliftYoneda.{u + 1}.map snd₀)
          (E.map (homOfLE (Nat.zero_le m))).hom g)
        {fstₙ : uliftYoneda.{u + 1}.obj c ⟶ (E.obj n).obj} {sndₙ : c ⟶ a}
        (_ : IsPullback fstₙ (uliftYoneda.{u + 1}.map sndₙ) (E.map (homOfLE hnm)).hom g),
        ((BigFppfOver.toScheme B S hS).map snd₀).ker ^ (n + 1) =
          ((BigFppfOver.toScheme B S hS).map sndₙ).ker) ∧
      ∃ e : X ≅ colimit E, IsReduction B S hS X (E.obj 0) (colimit.ι E 0 ≫ e.inv) := by
  classical
  let JT := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨Xred, i, hred⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX.1
  have hi := hred.isRepresentableThickening
  obtain ⟨I, Xi, f, -, hf, hcover, hNoeth⟩ := hX.2
  choose E ρ hρ hEaff hEred hEnoeth hw hci hker hloc using
    fun j ↦ exists_chain_of_isNoetherian (Xi j) (hNoeth j)
  -- the reductions of the charts, and the reduction of `X` pulled back to them
  let r (j : I) : yonedaSheaf B S hS ((E j).obj 0) ⟶ Xi j := ObjectProperty.homMk (ρ j 0)
  have hr (j : I) : IsReduction B S hS (Xi j) _ (r j) :=
    isReduction_of_isRepresentableThickening B S hS (r j)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS _)
      (hasEtaleLocalPropertyULift_isReduced_uliftYoneda B S hS _ (hEred j)) (hρ j 0)
  choose k hk using fun j ↦ exists_isPullback_of_isReduction_of_etale hred (hr j) (f j) (hf j)
  have hQ (j : I) : IsPullback (k j).hom (ρ j 0) i.hom (f j).hom :=
    (hk j).map (sheafToPresheaf JT (Type (u + 1)))
  -- the neighbourhoods of `X` along the charts are the stages of the charts
  have hmemj : ∀ (j : I) (n : ℕ) {T : BigFppfOver B S hS} (y : (Xi j).obj.obj (op T)),
      (f j).hom.app (op T) y ∈ (neighbourhood hi n).obj (op T) ↔
        y ∈ (Subfunctor.range (ρ j n)).obj (op T) := by
    intro j n T y
    rw [app_mem_neighbourhood_iff_of_isPullback hi (hρ j 0) (hQ j),
      neighbourhood_eq_range_of_chain (E j) (ρ j) (hρ j) (hw j) (hci j) (hker j) (hloc j) n]
  -- every section of `X` lies locally in a neighbourhood
  have hlocX : ∀ (T : BigFppfOver B S hS) (ξ : X.obj.obj (op T)),
      (⨆ n, (neighbourhood hi n).sieveOfSection ξ) ∈ JT T := by
    intro T ξ
    refine JT.transitive (family_imageSieve_mem JT Xi X f hcover T ξ) _ ?_
    intro V g hg
    obtain ⟨j, y, hy⟩ := (sieve_arrows_iSup_iff _ g).mp hg
    refine JT.superset_covering ?_ (hloc j V y)
    intro W g' hg'
    obtain ⟨m, hm⟩ := (sieve_arrows_iSup_iff _ g').mp hg'
    refine (sieve_arrows_iSup_iff _ (g' ≫ g)).mpr ⟨m, ?_⟩
    show X.obj.map (g' ≫ g).op ξ ∈ (neighbourhood hi m).obj (op W)
    rw [op_comp, Functor.map_comp_apply, ← hy, ← NatTrans.naturality_apply]
    exact (hmemj j m _).mpr hm
  -- the charts of the neighbourhoods
  have hX_n : ∀ n : ℕ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (neighbourhoodSheaf hi n).obj ∧
      Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (neighbourhoodSheaf hi n).obj
        (fun T : Scheme.{u} ↦ AlgebraicGeometry.IsLocallyNoetherian T) := by
    intro n
    let Rsp (j : I) : FppfSheaf B S hS := yonedaSheaf B S hS ((E j).obj n)
    let jj (j : I) : Rsp j ⟶ Xi j := ObjectProperty.homMk (ρ j n)
    have hle (j : I) : Subfunctor.range (ρ j n ≫ (f j).hom) ≤ neighbourhood hi n := by
      rintro T _ ⟨x, rfl⟩
      exact (hmemj j n _).mpr ⟨x, rfl⟩
    let kk (j : I) : Rsp j ⟶ neighbourhoodSheaf hi n :=
      ObjectProperty.homMk (Subfunctor.lift (ρ j n ≫ (f j).hom) (hle j))
    have hsq (j : I) : IsPullback (kk j) (jj j) (neighbourhoodι hi n) (f j) := by
      have hpre : IsPullback (kk j).hom (ρ j n) (neighbourhood hi n).ι (f j).hom :=
        isPullback_subfunctorι_of_forall _ _
          (mono_of_isRepresentableThickeningULift B S hS (hρ j n)) _ _
          (Subfunctor.lift_ι (ρ j n ≫ (f j).hom) (hle j))
          (fun T y hy ↦ (hmemj j n y).mp hy)
      exact IsPullback.of_map (sheafToPresheaf JT (Type (u + 1)))
        ((sheafToPresheaf JT (Type (u + 1))).map_injective hpre.w) hpre
    have hcoverR : Sheaf.IsLocallySurjective (Sigma.desc kk) := by
      constructor
      intro T x
      refine JT.superset_covering ?_ (family_imageSieve_mem JT Xi X f hcover T x.1)
      intro V g hg
      obtain ⟨j, y, hy⟩ := (sieve_arrows_iSup_iff _ g).mp hg
      have hyn : y ∈ (Subfunctor.range (ρ j n)).obj (op V) := by
        rw [← hmemj, hy]
        exact (neighbourhood hi n).map g.op x.2
      obtain ⟨z, hz⟩ := hyn
      refine ⟨(Sigma.ι (fun j ↦ Rsp j) j).hom.app (op V) z, ?_⟩
      apply Subtype.ext
      show ((Sigma.ι (fun j ↦ Rsp j) j ≫ Sigma.desc kk).hom.app (op V) z).1 = _
      rw [show Sigma.ι (fun j ↦ Rsp j) j ≫ Sigma.desc kk = kk j from Sigma.ι_desc _ _]
      show (f j).hom.app (op V) ((ρ j n).app (op V) z) = _
      rw [hz, hy]
      rfl
    have halg := isAlgebraicSpaceULift_of_reduced_etale_cover B S hS (neighbourhoodι hi n)
      (mono_neighbourhoodι_hom hi n) hX.1 Xi Rsp (fun j ↦ (E j).obj n) (fun j ↦ hEaff j n)
      (fun j ↦ Iso.refl _) f kk jj hsq
      hf hcoverR (isRepresentableThickeningULift_neighbourhoodι hi n)
    exact ⟨halg, hasEtaleLocalPropertyULift_isLocallyNoetherian_of_etale_charts halg
      (fun j ↦ (E j).obj n) (fun j ↦ hEnoeth j n)
      (fun j ↦ (Iso.refl (uliftYoneda.{u + 1}.obj ((E j).obj n))).hom ≫ (kk j).hom)
      (fun j ↦ relative_etale_of_isPullback B S hS (neighbourhoodι hi n) (f j) (kk j) (jj j)
        (hsq j) (hf j) ((E j).obj n) (Iso.refl _)
        (Functor.relativelyRepresentable.of_diag halg.diagonal_representable _))
      (family_imageSieve_mem JT Rsp (neighbourhoodSheaf hi n) kk hcoverR)⟩
  -- the colimit
  have := isIso_colimitDesc_neighbourhoodCocone hi hlocX
  let e : X ≅ colimit (neighbourhoodDiagram hi) :=
    (asIso (colimit.desc (neighbourhoodDiagram hi) (neighbourhoodCocone hi))).symm
  refine ⟨neighbourhoodDiagram hi, fun n ↦ (hX_n n).1, fun n ↦ (hX_n n).2,
    fun n m f ↦ hasSchemePropertyULift_isNthOrderThickening_neighbourhoodDiagram hi f,
    fun n m hnm a b c g fst₀ snd₀ sq₀ fstₙ sndₙ sqₙ ↦
      ker_pow_eq_ker_neighbourhoodDiagram hi n m hnm g sq₀ sqₙ, e, ?_⟩
  rw [show colimit.ι (neighbourhoodDiagram hi) 0 ≫ e.inv = neighbourhoodι hi 0 from
    colimit.ι_desc (neighbourhoodCocone hi) 0]
  exact IsReduction.neighbourhoodι_zero hi hred

end AlgebraicGeometry.FormalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.StageThickening
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence

/-!
# The infinitesimal neighbourhoods of the reduction are algebraic spaces

Let `W` be a locally Noetherian formal algebraic space with reduction `i : W_red ⟶ W`, and let
`W_k ⊆ W` be the `k`-th infinitesimal neighbourhood of `W_red`
(`AlgebraicGeometry.FormalSpace.reductionNeighbourhood`). Over a Noetherian affine formal chart
`Spf A ⟶ W` the subsheaf `W_k` pulls back to the stage `Spec(A/𝔞^(k+1))`, which is an affine
scheme and a representable thickening of `Spf A`. Hence the inclusion `W_k ⟶ W` is a
representable thickening and `W_k` is a locally Noetherian algebraic space. For `k = 0` the
stages `Spec(A/𝔞)` are reduced, so `W_0` is a reduction of `W`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_reductionNeighbourhood`: `W_k` is an
  algebraic space.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_reductionNeighbourhood_ι`: the
  inclusion `W_k ⟶ W` is a representable thickening.
* `AlgebraicGeometry.FormalSpace.isReduction_reductionNeighbourhood_zero`: `W_0` is a reduction
  of `W`.
* `hasEtaleLocalPropertyULift_isLocallyNoetherian_reductionNeighbourhood`: `W_k` has a surjective
  étale atlas by a locally Noetherian scheme.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe w u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {W Wred : FppfSheaf B S hS} (i : Wred ⟶ W)

/-- The `k`-th infinitesimal neighbourhood `W_k` of the reduction, as an fppf sheaf. -/
abbrev reductionNeighbourhoodSheaf (k : ℕ) : FppfSheaf B S hS :=
  ⟨(reductionNeighbourhood i k).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_reductionNeighbourhood k)⟩

/-- The inclusion `W_k ⟶ W`. -/
abbrev reductionNeighbourhoodι (k : ℕ) : reductionNeighbourhoodSheaf i k ⟶ W :=
  ⟨(reductionNeighbourhood i k).ι⟩

variable {i}

/-- The range of a morphism is unchanged by precomposing with an isomorphism. -/
private theorem range_comp_of_isIso {C : Type*} [Category C] {F G H : C ⥤ Type w}
    (e : F ⟶ G) [IsIso e] (g : G ⟶ H) : Subfunctor.range (e ≫ g) = Subfunctor.range g := by
  ext T y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.app T x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(inv e).app T x, ?_⟩
    change (inv e ≫ e ≫ g).app T x = _
    rw [IsIso.inv_hom_id_assoc]

/-- Relative representability by `uliftYoneda` of the pullback of a property along `toScheme`
respects isomorphisms. -/
private theorem respectsIso_relative_uliftYoneda_inverseImage (P : MorphismProperty Scheme.{u}) :
    (MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).RespectsIso :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1})
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).respectsIso

/-- For `W` locally Noetherian with reduction `i`, the inclusion of `W_k` is a representable
thickening, `W_k` is an algebraic space, it has a reduced étale atlas when `k = 0`, and it has a
locally Noetherian étale atlas. -/
private theorem reductionNeighbourhood_main (hW : IsLocallyNoetherian B S hS W)
    (hred : IsReduction B S hS W Wred i) (k : ℕ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (reductionNeighbourhoodι i k).hom ∧
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS (reductionNeighbourhoodSheaf i k).obj ∧
      (k = 0 → Space.HasEtaleLocalPropertyULift.{u + 1} B S hS
        (reductionNeighbourhoodSheaf i k).obj (fun T : Scheme.{u} => IsReduced T)) ∧
      Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (reductionNeighbourhoodSheaf i k).obj
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) := by
  classical
  let J := BigFppfOver.topology B S hS
  obtain ⟨I, c, hcover⟩ := exists_presentedEtaleCharts hW
  let Xi (j : I) : FppfSheaf B S hS := formalSpectrum (c j).system
  let f (j : I) : Xi j ⟶ W := (c j).chart
  have hf (j : I) : ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f j).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f j).hom hfi :=
    ⟨(c j).representable, (c j).etale⟩
  let Ti (j : I) : BigFppfOver B S hS := (c j).system.stageObj ((c j).powStage k)
  let Rsp (j : I) : FppfSheaf B S hS :=
    ⟨uliftYoneda.{u + 1}.obj (Ti j),
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (Ti j)).isSheaf⟩
  let jj (j : I) : Rsp j ⟶ Xi j :=
    (sheafificationIso (Rsp j)).hom ≫ stageIncl (c j).system ((c j).powStage k)
  have hjj (j : I) : Space.IsRepresentableThickeningULift.{u + 1} B S hS (jj j).hom := by
    have := respectsIso_relative_uliftYoneda_inverseImage (B := B) (S := S) (hS := hS)
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    exact MorphismProperty.RespectsIso.precomp _ (sheafificationIso (Rsp j)).hom.hom _
      (isRepresentableThickeningULift_stageIncl (c j).weaklyAdmissible (c j).system _)
  have hjjmono (j : I) : Mono (jj j).hom :=
    mono_of_isRepresentableThickeningULift B S hS (hjj j)
  have hrange (j : I) : Subfunctor.range (jj j ≫ f j).hom =
      Subfunctor.range (stageIncl (c j).system ((c j).powStage k) ≫ (c j).chart).hom := by
    change Subfunctor.range ((sheafificationIso (Rsp j)).hom.hom ≫
      (stageIncl (c j).system ((c j).powStage k) ≫ (c j).chart).hom) = _
    exact range_comp_of_isIso _ _
  have heq : reductionNeighbourhood i k =
      (⨆ j, Subfunctor.range (jj j ≫ f j).hom).sheafify J := by
    rw [reductionNeighbourhood_eq_sheafify hred c hcover k]
    simp only [hrange]
    rfl
  let R := reductionNeighbourhoodSheaf i k
  let ι := reductionNeighbourhoodι i k
  have hle (j : I) : Subfunctor.range (jj j ≫ f j).hom ≤ reductionNeighbourhood i k := by
    rw [heq]
    exact (le_iSup (fun j => Subfunctor.range (jj j ≫ f j).hom) j).trans
      (Subfunctor.le_sheafify _ _)
  let kk (j : I) : Rsp j ⟶ R := ⟨Subfunctor.lift (jj j ≫ f j).hom (hle j)⟩
  have hk (j : I) : kk j ≫ ι = jj j ≫ f j :=
    (sheafToPresheaf J (Type (u + 1))).map_injective (Subfunctor.lift_ι (jj j ≫ f j).hom (hle j))
  have hιmono : Mono ι.hom := inferInstanceAs (Mono (reductionNeighbourhood i k).ι)
  have hsq (j : I) : IsPullback (kk j) (jj j) ι (f j) := by
    refine isPullback_of_mono_of_local_lift B S hS _ _ _ _ (hk j) (hjjmono j)
      fun T x y hxy => ⟨⊤, J.top_mem T, fun T' h _ => ?_⟩
    obtain ⟨z, hz⟩ :
        y ∈ (Subfunctor.range (stageIncl (c j).system ((c j).powStage k)).hom).obj (op T) :=
      ((c j).mem_range_powStage_iff_mem hred k y).2 (hxy ▸ x.property)
    let z' : (Rsp j).obj.obj (op T) := (sheafificationIso (Rsp j)).inv.hom.app _ z
    have hz' : (jj j).hom.app (op T) z' = y := by
      change ((sheafificationIso (Rsp j)).inv ≫ (sheafificationIso (Rsp j)).hom ≫
        stageIncl (c j).system ((c j).powStage k)).hom.app (op T) z = y
      rw [show (sheafificationIso (Rsp j)).inv ≫ (sheafificationIso (Rsp j)).hom ≫
        stageIncl (c j).system ((c j).powStage k) = stageIncl (c j).system ((c j).powStage k)
        from Iso.inv_hom_id_assoc _ _]
      exact hz
    refine ⟨(Rsp j).obj.map h.op z', ?_, ?_⟩
    · rw [NatTrans.naturality_apply]
      congr 1
      apply Subtype.ext
      refine (ConcreteCategory.congr_hom (congr_app
        (congrArg (fun t : Rsp j ⟶ W => t.hom) (hk j)) (op T)) z').trans ?_
      change (f j).hom.app (op T) ((jj j).hom.app (op T) z') = x.val
      rw [hz']
      exact hxy.symm
    · rw [NatTrans.naturality_apply, hz']
  have hcoverR : Sheaf.IsLocallySurjective (Sigma.desc kk) := by
    refine (Sheaf.isLocallySurjective_sigmaDesc_iff kk).2 fun T x => ?_
    have hx : x.val ∈ ((⨆ j, Subfunctor.range (jj j ≫ f j).hom).sheafify J).obj (op T) :=
      heq ▸ x.property
    refine ⟨_, hx, fun V g hg => ?_⟩
    change W.obj.map g.op x.val ∈ (⨆ j, Subfunctor.range (jj j ≫ f j).hom).obj (op V) at hg
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj] at hg
    obtain ⟨j, y, hy⟩ := hg
    exact ⟨j, y, Subtype.ext hy⟩
  have hιthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom :=
    isRepresentableThickeningULift_of_isPullback_etale_cover B S hS ι hιmono Xi Rsp f kk jj hsq hf
      hcover hjj
  have halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj :=
    isAlgebraicSpaceULift_of_reduced_etale_cover B S hS ι hιmono hW.1 Xi Rsp Ti
      (fun j => inferInstanceAs (IsAffine (Spec _))) (fun j => Iso.refl _) f kk jj hsq hf
      hcoverR hιthick
  have hnoeth : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS R.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) := by
    obtain ⟨U, p, hps, hpe⟩ := halg.exists_atlas
    refine ⟨U, p, hps, hpe, ?_⟩
    let C := BigFppfOver B S hS
    let Y := uliftYoneda.{u + 1} (C := C)
    let q := BigFppfOver.toScheme B S hS
    let P : MorphismProperty C :=
      MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) q
    let : MorphismProperty.RespectsIso (@Etale.{u}) := .mk _
      (fun e f hf => by have := hf; infer_instance)
      (fun e f hf => by have := hf; infer_instance)
    let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
    let : HasBinaryProducts C := Over.ConstructProducts.over_binaryProduct_of_pullback
    have hdiagR := uliftYoneda_relativelyRepresentable_diag_of_mono B S hS ι hιmono
      (uliftYoneda_relativelyRepresentable_diag B S hS hW.1)
    let gi (j : I) : Y.obj (Ti j) ⟶ R.obj := (Iso.refl (Rsp j).obj).hom ≫ (kk j).hom
    have hgi (j : I) : P.relative Y (gi j) :=
      relative_etale_of_isPullback B S hS ι (f j) (kk j) (jj j) (hsq j) (hf j) (Ti j)
        (Iso.refl _) (Functor.relativelyRepresentable.of_diag hdiagR _)
    let Vj (j : I) : C := (hgi j).rep.pullback p
    let pj (j : I) : Vj j ⟶ U := (hgi j).rep.snd p
    let rj (j : I) : Vj j ⟶ Ti j := Y.preimage ((hgi j).rep.fst p)
    have hpj (j : I) : Etale (q.map (pj j)) := (hgi j).property_snd p
    have hrj (j : I) : Etale (q.map (rj j)) := by
      refine hpe.2 (gi j) (Y.map (pj j)) (rj j) ?_
      rw [Y.map_preimage]
      exact ((hgi j).rep.isPullback p).flip
    have hVj (j : I) : _root_.AlgebraicGeometry.IsLocallyNoetherian (q.obj (Vj j)) := by
      have : _root_.AlgebraicGeometry.IsLocallyNoetherian (q.obj (Ti j)) := by
        change _root_.AlgebraicGeometry.IsLocallyNoetherian
          (Spec (.of ((c j).ring ⧸ topologicalNilradical (c j).ring ^ (k + 1))))
        infer_instance
      have := hrj j
      exact LocallyOfFiniteType.isLocallyNoetherian (q.map (rj j))
    have hpoint : ∀ x : q.obj U, ∃ j, x ∈ Set.range (q.map (pj j)) := by
      have hmem := family_imageSieve_mem J Rsp R kk hcoverR U (uliftYonedaEquiv p)
      rw [GrothendieckTopology.mem_over_iff] at hmem
      obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hmem
      have hEF := B.isFppfCovering_of_isCovering hE
      rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
        PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
        Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
      intro x
      obtain ⟨l, y, hy⟩ := hEF.1 x
      let T : C := Over.mk (E.f l ≫ U.hom)
      let b : T ⟶ U := Over.homMk (E.f l)
      have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨l⟩)
      change (⨆ j, Presheaf.imageSieve (kk j).hom (uliftYonedaEquiv p)) b at hb
      simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
      obtain ⟨-, ⟨j, rfl⟩, z, hz⟩ := hb
      let m : Y.obj T ⟶ (Rsp j).obj := uliftYonedaEquiv.symm z
      have hw : m ≫ gi j = Y.map b ≫ p := by
        simp only [gi, Iso.refl_hom]
        apply uliftYonedaEquiv.injective
        rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
        exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} p b.op)
      let a : T ⟶ Vj j := Y.preimage (((hgi j).rep.isPullback p).lift m (Y.map b) hw)
      have hab : a ≫ pj j = b := by
        apply Y.map_injective
        rw [Y.map_comp, Y.map_preimage]
        exact ((hgi j).rep.isPullback p).lift_snd _ _ _
      refine ⟨j, a.left.hom y, ?_⟩
      change ((q.map a) ≫ q.map (pj j)) y = x
      rw [← Functor.map_comp, hab]
      exact hy
    choose idx hidx using hpoint
    exact ObjectProperty.of_presieve (K := Scheme.etalePrecoverage)
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2
        ⟨fun x => ⟨x, hidx x⟩, fun x => hpj (idx x)⟩)
      (by rintro _ _ ⟨x⟩; exact hVj (idx x))
  refine ⟨hιthick, halg, fun hk0 => ?_, hnoeth⟩
  subst hk0
  obtain ⟨T, atlas, hs, he⟩ := halg.exists_atlas
  have hTired (j : I) : IsReduced ((BigFppfOver.toScheme B S hS).obj (Ti j)) := by
    change IsReduced (Spec (.of ((c j).ring ⧸ topologicalNilradical (c j).ring ^ (0 + 1))))
    have : _root_.IsReduced ((c j).ring ⧸ topologicalNilradical (c j).ring ^ (0 + 1)) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp
        (by simpa using TopologicalRing.topologicalNilradical_isRadical (B := (c j).ring))
    infer_instance
  refine ⟨T, atlas, hs, he, ?_⟩
  let e : (reductionNeighbourhood i 0).toFunctor ⟶
      ((⨆ j, Subfunctor.range (jj j ≫ f j).hom).sheafify J).toFunctor :=
    Subfunctor.homOfLe heq.le
  have : IsIso e := by
    refine ⟨Subfunctor.homOfLe heq.ge, ?_, ?_⟩ <;> ext <;> rfl
  have hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (atlas ≫ e) := by
    have := respectsIso_relative_uliftYoneda_inverseImage (B := B) (S := S) (hS := hS)
      (@Etale.{u} : MorphismProperty Scheme.{u})
    exact MorphismProperty.RespectsIso.postcomp _ e atlas he
  exact isReduced_of_isEtale_into_sheafified_iSup_range B S hS W.obj Ti hTired
    (fun j => (jj j ≫ f j).hom) T (atlas ≫ e) hpe

/-- **The inclusion `W_k ⟶ W` is a representable thickening.** -/
theorem isRepresentableThickeningULift_reductionNeighbourhood_ι
    (hW : IsLocallyNoetherian B S hS W) (hred : IsReduction B S hS W Wred i) (k : ℕ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (reductionNeighbourhoodι i k).hom :=
  (reductionNeighbourhood_main hW hred k).1

/-- **`W_k` is an algebraic space.** -/
theorem isAlgebraicSpaceULift_reductionNeighbourhood
    (hW : IsLocallyNoetherian B S hS W) (hred : IsReduction B S hS W Wred i) (k : ℕ) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (reductionNeighbourhoodSheaf i k).obj :=
  (reductionNeighbourhood_main hW hred k).2.1

/-- **`W_0` is a reduction of `W`.** -/
theorem isReduction_reductionNeighbourhood_zero
    (hW : IsLocallyNoetherian B S hS W) (hred : IsReduction B S hS W Wred i) :
    IsReduction B S hS W (reductionNeighbourhoodSheaf i 0) (reductionNeighbourhoodι i 0) :=
  isReduction_of_isRepresentableThickening B S hS _
    (isAlgebraicSpaceULift_reductionNeighbourhood hW hred 0)
    ((reductionNeighbourhood_main hW hred 0).2.2.1 rfl)
    (isRepresentableThickeningULift_reductionNeighbourhood_ι hW hred 0)

/-- **`W_k` is a locally Noetherian algebraic space:** it has a surjective étale atlas by a
locally Noetherian scheme. -/
theorem hasEtaleLocalPropertyULift_isLocallyNoetherian_reductionNeighbourhood
    (hW : IsLocallyNoetherian B S hS W) (hred : IsReduction B S hS W Wred i) (k : ℕ) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (reductionNeighbourhoodSheaf i k).obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
  (reductionNeighbourhood_main hW hred k).2.2.2

end AlgebraicGeometry.FormalSpace

end

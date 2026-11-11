module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationFibreTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceTowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion

/-!
# Algebraizing the closure of an étale chart over the source

This is step 3 of the design of the quasi-separated case of Stacks 0GHK
(`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`), up to the
algebraization of the closed tower.

Let `A` be a Noetherian ring complete with respect to `I`, `X` proper over `S = Spec A`, `Y` an
algebraic space over `S` and `g_n : X_n ⟶ Y_n` a compatible system, with composites
`φ_n : X_n ⟶ Y_n ⟶ Y`. Let `π̄ : V̄ ⟶ Y` be finite, `P` a scheme proper over `S` and
`c : Ṽ ⟶ V̄ ×_S P` a closed immersion. Then:

* the finite morphisms `X_n ×_Y V̄ ⟶ X_n` form a cartesian tower, which algebraizes to a finite
  `π : F ⟶ X` (Stacks 0A01), with `u_n : F_n ⟶ V̄` exhibiting `F_n = X_n ×_Y V̄`;
* with `M = F ×_S P` and `h_n : M_n ⟶ V̄ ×_S P` induced by the `u_n`, the closed subspaces
  `M_n ×_{V̄ ×_S P} Ṽ` of the `M_n` form a cartesian tower, proper over `S_0` at the bottom, which
  algebraizes to a closed subspace `W ⊆ M` proper over `S` (Stacks 08BG).

## Main results

* `AlgebraicGeometry.Space.exists_algebraization_chartClosure`: the two algebraizations.

## References

* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))}

/-- **Algebraizing the closure of an étale chart over the source.** Let `A` be Noetherian and
`I`-adically complete, `X` proper over `S = Spec A`, `g_n : X_n ⟶ Y_n` a compatible system with
composites `φ_n : X_n ⟶ Y`, `π̄ : V̄ ⟶ Y` finite, `P` proper over `S` and `c : Ṽ ⟶ V̄ ×_S P` a
closed immersion. There are a finite `π : F ⟶ X` with `F` proper over `S` and morphisms
`u_n : F_n ⟶ V̄`, compatible with the transitions, exhibiting `F_n` as `X_n ×_Y V̄`; and a closed
subspace `i : W ⟶ F ×_S P` proper over `S` whose adic fibres are identified, compatibly with the
transitions, with the closed subspaces `(F ×_S P)_n ×_{V̄ ×_S P} Ṽ` of the adic fibres of
`F ×_S P`, where `(F ×_S P)_n ⟶ V̄ ×_S P` is induced by `u_n`. -/
theorem exists_algebraization_chartClosure [IsNoetherianRing A] [IsAdicComplete I A]
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX)
    (g : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) fX n ⟶
      adicFibre A I B hS (contains_adicThickening A I B hS) fY n)
    (hgc : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS (contains_adicThickening A I B hS) fY n)
    {P : BigFppfOver B (Spec (.of A)) hS} (p : P ⟶ baseObject A B hS)
    (hp : IsProper B _ hS (yoneda.map p))
    {Vb Vt : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hVb : IsAlgebraicSpace B _ hS Vb)
    (hVt : IsAlgebraicSpace B _ hS Vt) (πb : Vb ⟶ Y) (hπb : IsFinite B _ hS πb)
    (c : Vt ⟶ pullback (πb ≫ fY) (yoneda.map p)) (hc : IsClosedImmersion B _ hS c) :
    ∃ (F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B _ hS F)
      (π : F ⟶ X)
      (u : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ⟶ Vb),
      IsFinite B _ hS π ∧ IsProper B _ hS (π ≫ fX) ∧
      (∀ n, IsPullback (u n) (adicFibreMap A I B hS (contains_adicThickening A I B hS) π rfl n)
        πb (g n ≫ pullback.fst fY
          (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)))) ∧
      ∃ (hu : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ≫
          u (n + 1) = u n)
        (W : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B _ hS W)
        (i : W ⟶ pullback (π ≫ fX) (yoneda.map p)),
        IsClosedImmersion B _ hS i ∧
        IsProper B _ hS (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) ∧
        ∃ e : ∀ n, pullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c ≅
            adicFibre A I B hS (contains_adicThickening A I B hS)
              (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n,
          (∀ n, (e n).hom ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n =
            pullback.fst _ _) ∧
          (∀ n, fibreTowerSucc (fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
              (adicFibreSucc_adicFibreProdMap p u hu) c n ≫ (e (n + 1)).hom =
            (e n).hom ≫ adicFibreSucc A I B hS (contains_adicThickening A I B hS)
              (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n) := by
  have hSn := contains_adicThickening A I B hS
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  have hPyo := isAlgebraicSpace_yoneda B _ hS P
  have hTh : ∀ n, IsAlgebraicSpace B _ hS
      (yoneda.obj (adicThickeningObject A I B hS (contains_adicThickening A I B hS) n)) :=
    fun n => isAlgebraicSpace_yoneda B _ hS _
  let φ : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) fX n ⟶ Y := fun n =>
    g n ≫ pullback.fst fY
      (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n))
  have hφ : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) fX n ≫ φ (n + 1) =
      φ n := fun n => by
    simp only [φ]
    rw [reassoc_of% (hgc n), adicFibreSucc_fst]
  have hXn : ∀ n, IsAlgebraicSpace B _ hS
      (adicFibre A I B hS (contains_adicThickening A I B hS) fX n) :=
    isAlgebraicSpace_adicFibre A I B hS _ hX fX
  have hTn : ∀ n, IsAlgebraicSpace B _ hS (pullback (φ n) πb) := fun n =>
    isAlgebraicSpace_pullback B _ hS _ _ (hXn n) hVb hY
  -- Stacks 0A01 for the finite tower `X_n ×_Y V̄`
  have hfin0 : IsFinite B _ hS (pullback.fst (φ 0) πb) :=
    isFinite_of_isPullback B _ hS (IsPullback.of_hasPullback (φ 0) πb).flip hπb
  have hprop0 : IsProper B _ hS (pullback.fst (φ 0) πb ≫ adicFibreSnd A I B hS fX 0) :=
    isProper_comp' B _ hS _ _ (hXn 0) (hTh 0)
      ((isFinite_iff_isAffineHom_and_isProper B _ hS (hTn 0) (hXn 0) _).mp hfin0).2
      (isProper_pullback_snd B _ hS hX hbase (hTh 0) fX _ hpX)
  obtain ⟨Fs, π, hπfin, hπprop, e, he1, he2, -⟩ :=
    exists_isFinite_adicFibre_iso_of_tower A I B hS hX fX hpX.1 hpX.2.1
      (fun n => ⟨pullback (φ n) πb, hTn n⟩)
      (fun n => ObjectProperty.homMk (pullback.fst (φ n) πb))
      (fun n => ObjectProperty.homMk (fibreTowerSucc φ hφ πb n))
      (fun n => IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B (Spec (.of A)) hS F))
        (isPullback_fibreTowerSucc φ hφ πb n))
      hfin0 hprop0
  let ε : ∀ n, pullback (φ n) πb ≅
      adicFibre A I B hS (contains_adicThickening A I B hS) (π.hom ≫ fX) n := fun n =>
    (ObjectProperty.ι _).mapIso (e n)
  let u : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) (π.hom ≫ fX) n ⟶ Vb :=
    fun n => (ε n).inv ≫ pullback.snd (φ n) πb
  have hεfst : ∀ n, (ε n).hom ≫
      adicFibreMap A I B hS (contains_adicThickening A I B hS) π.hom rfl n =
        pullback.fst (φ n) πb := he1
  have hεsucc : ∀ n, fibreTowerSucc φ hφ πb n ≫ (ε (n + 1)).hom =
      (ε n).hom ≫ adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π.hom ≫ fX) n :=
    fun n => congrArg (·.hom) (he2 n)
  have hu : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π.hom ≫ fX) n ≫
      u (n + 1) = u n := by
    intro n
    have h : (ε n).inv ≫ fibreTowerSucc φ hφ πb n =
        adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π.hom ≫ fX) n ≫
          (ε (n + 1)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hεsucc n, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    simp only [u]
    rw [← Category.assoc, ← h, Category.assoc, fibreTowerSucc_snd]
  have hsqu : ∀ n, IsPullback (u n)
      (adicFibreMap A I B hS (contains_adicThickening A I B hS) π.hom rfl n) πb (φ n) := by
    intro n
    refine IsPullback.of_iso (IsPullback.of_hasPullback (φ n) πb).flip (ε n) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [u]
    · rw [hεfst n, Iso.refl_hom, Category.comp_id]
    · simp
    · simp
  -- the adic fibres of `M = F ×_S P`
  let fF := π.hom ≫ fX
  let h : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS)
      (pullback.fst fF (yoneda.map p) ≫ fF) n ⟶ pullback (πb ≫ fY) (yoneda.map p) :=
    fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n)
  have hh := adicFibreSucc_adicFibreProdMap (fQ := πb ≫ fY) p u hu
  have hM : IsAlgebraicSpace B _ hS (pullback fF (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ Fs.2 hPyo hbase
  let fM := pullback.fst fF (yoneda.map p) ≫ fF
  have hfstM : IsProper B _ hS (pullback.fst fF (yoneda.map p)) :=
    isProper_pullback_fst B _ hS hPyo hbase Fs.2 (yoneda.map p) fF hp
  have hfM : IsProper B _ hS fM := isProper_comp' B _ hS _ _ Fs.2 hbase hfstM hπprop
  have hMn : ∀ n, IsAlgebraicSpace B _ hS
      (adicFibre A I B hS (contains_adicThickening A I B hS) fM n) :=
    isAlgebraicSpace_adicFibre A I B hS _ hM fM
  have hFn : ∀ n, IsAlgebraicSpace B _ hS
      (adicFibre A I B hS (contains_adicThickening A I B hS) fF n) :=
    isAlgebraicSpace_adicFibre A I B hS _ Fs.2 fF
  have hVbP : IsAlgebraicSpace B _ hS (pullback (πb ≫ fY) (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ hVb hPyo hbase
  have hZ' : ∀ n, IsAlgebraicSpace B _ hS (pullback (h n) c) := fun n =>
    isAlgebraicSpace_pullback B _ hS _ _ (hMn n) hVt hVbP
  have hj0 : IsClosedImmersion B _ hS (pullback.fst (h 0) c) := by
    have := isClosedImmersion_isStableUnderBaseChange B (Spec (.of A)) hS
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback (h 0) c).flip hc
  -- the bottom of the closed tower is proper over `S_0`
  have haM : IsProper B _ hS
      (adicFibreMap A I B hS (contains_adicThickening A I B hS)
        (pullback.fst fF (yoneda.map p)) rfl 0) :=
    isProper_snd_of_isPullback (hMn 0) hPyo (hFn 0) hbase (isPullback_adicFibre_pullback p 0) hp
  have haF : IsProper B _ hS
      (adicFibreMap A I B hS (contains_adicThickening A I B hS) π.hom rfl 0) :=
    ((isFinite_iff_isAffineHom_and_isProper B _ hS (hFn 0) (hXn 0) _).mp
      (isFinite_of_isPullback B _ hS (isPullback_adicFibreMap_fst π.hom 0) hπfin)).2
  have hsnd0 : IsProper B _ hS (adicFibreSnd A I B hS fX 0) :=
    isProper_pullback_snd B _ hS hX hbase (hTh 0) fX _ hpX
  have hprop' : IsProper B _ hS (pullback.fst (h 0) c ≫ pullback.snd fM
      (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) 0))) := by
    have e1 : pullback.snd fM
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) 0)) =
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (pullback.fst fF (yoneda.map p)) rfl 0 ≫
          adicFibreMap A I B hS (contains_adicThickening A I B hS) π.hom rfl 0 ≫
            adicFibreSnd A I B hS fX 0 := by
      simp [fM, fF]
    rw [e1]
    exact isProper_comp' B _ hS _ _ (hMn 0) (hTh 0)
      (isProper_of_isClosedImmersion B _ hS (hZ' 0) (hMn 0) _ hj0)
      (isProper_comp' B _ hS _ _ (hFn 0) (hTh 0) haM
        (isProper_comp' B _ hS _ _ (hXn 0) (hTh 0) haF hsnd0))
  -- Stacks 08BG for the closed tower `M_n ×_{V̄ ×_S P} Ṽ`
  obtain ⟨W, hW, i, hi, hWp, e', he'1, he'2⟩ :=
    exists_isClosedImmersion_adicFibre_iso A I B hS (contains_adicThickening A I B hS) hM fM
      hfM.2.1 hfM.1 (fun n => pullback (h n) c) hZ' (fun n => pullback.fst (h n) c)
      (fibreTowerSucc h hh c) (isPullback_fibreTowerSucc h hh c) hj0 hprop'
  exact ⟨Fs.1, Fs.2, π.hom, u, hπfin, hπprop, hsqu, hu, W, hW, i, hi, hWp, e', he'1, he'2⟩

end AlgebraicGeometry.Space

end

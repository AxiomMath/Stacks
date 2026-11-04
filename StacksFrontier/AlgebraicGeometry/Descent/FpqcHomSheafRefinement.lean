module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of morphisms of quasi-coherent modules along fpqc coverings

This file proves `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the full-faithfulness half
of Stacks 023T in the form Stacks 03DT consumes it: for every fpqc covering family of a scheme
`S` and all quasi-coherent modules `M` and `N` on `S`, pulling morphisms `M ⟶ N` back to the
family is a bijection onto the morphisms of the associated descent data.  Equivalently
(`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms_iff_isSheaf_presheafHom`) it is the single
assertion that the presheaf of morphisms `T ⟶ S ↦ (T^* M ⟶ T^* N)` is an fpqc sheaf on the
schemes over `S`.

## Main results

* `AlgebraicGeometry.isSeparatedFor_presheafHom_fpqc`: the presheaf of morphisms of
  quasi-coherent modules is separated for every fpqc covering family of every object of the
  schemes over `S`.
* `AlgebraicGeometry.exists_isSeparatedFor_factorsThruAlong_fpqc`: a separated refinement of a
  presieve refined by an fpqc covering family, over an arbitrary object mapping in.
* `AlgebraicGeometry.isSheafFor_presheafHom_standardAffine_over`: the sheaf condition for the
  standard affine covering attached to a faithfully flat map into a finite product of rings,
  over an arbitrary object `Over.mk a` of the schemes over `S`.
* `AlgebraicGeometry.isSheafFor_presheafHom_fpqc`: the sheaf condition for the presheaf of
  morphisms, for an arbitrary fpqc covering family of `S`.
* `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`:
  **`AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms` holds.**
* `AlgebraicGeometry.isSheaf_presheafHom'`,
  `AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'` and the five
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_*'` theorems: the consequences in
  `StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic`, with their hypothesis
  `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms` discharged.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The presieve on an object `Y` of the schemes over `S` attached to a family of morphisms
`u i : U i ⟶ Y.left`.  This is `AlgebraicGeometry.overPresieve` over an arbitrary object. -/
abbrev overPresieveOn (Y : Over S) {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Y.left) :
    Presieve Y :=
  Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ Y.hom)) (fun i ↦ (Over.homMk (u i) : _ ⟶ Y))

/-- **The affine opens are a Zariski covering.**  The family of morphisms
`Spec Γ(V, ⊤) ⟶ X` indexed by the affine opens `V` of `X`, each the inverse of
`AlgebraicGeometry.Scheme.isoSpec` followed by the inclusion, is a jointly surjective family of
open immersions. -/
lemma ofArrows_affineOpens_mem_zariskiPrecoverage (X : Scheme.{u}) :
    Presieve.ofArrows (fun V : X.affineOpens ↦ Spec Γ(V.1.toScheme, ⊤))
      (fun V ↦ V.1.toScheme.isoSpec.inv ≫ V.1.ι) ∈ Scheme.zariskiPrecoverage.{u} X := by
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun V ↦ inferInstance⟩
  have hx : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at hx
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ : x ∈ Set.range V.1.ι.base := by rw [V.1.range_ι]; exact hV
  refine ⟨V, V.1.toScheme.isoSpec.hom.base y, ?_⟩
  simpa [Scheme.Hom.comp_apply] using hy

/-- The open immersion of the `k`-th factor of a finite product of affine schemes, as the
morphism of spectra induced by the evaluation map of the product ring. -/
noncomputable abbrev specPiEval {n : ℕ} (B : Fin n → CommRingCat.{u}) (k : Fin n) :
    Spec (B k) ⟶ Spec (CommRingCat.of (∀ j : Fin n, (B j : Type u))) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : Fin n ↦ (B j : Type u)) k))

/-- **The spectrum of a finite product of rings is covered by the spectra of the factors.**  The
evaluation maps of a finite product of commutative rings induce a jointly surjective family of
open immersions of spectra. -/
lemma ofArrows_specPiEval_mem_zariskiPrecoverage {n : ℕ} (B : Fin n → CommRingCat.{u}) :
    Presieve.ofArrows (fun k ↦ Spec (B k)) (specPiEval B) ∈
      Scheme.zariskiPrecoverage.{u} (Spec (CommRingCat.of (∀ k : Fin n, (B k : Type u)))) := by
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun p ↦ ?_, fun k ↦ inferInstance⟩
  obtain ⟨k, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (R := fun k : Fin n ↦ (B k : Type u)) p
  exact ⟨k, q, by rw [specPiEval, Spec.map_base]; exact hq⟩

/-- The map from the global sections of a scheme to the product of the global sections of a
finite family of affine schemes over it. -/
@[sga "3 VIB 11.9.1"]
noncomputable abbrev piAppTopHom {W : Scheme.{u}} {n : ℕ} {A : Fin n → CommRingCat.{u}}
    (g : ∀ k, Spec (A k) ⟶ W) :
    Γ(W, ⊤) ⟶ CommRingCat.of (∀ k : Fin n, (Γ(Spec (A k), ⊤) : Type u)) :=
  CommRingCat.ofHom (RingHom.pi fun k ↦ (g k).appTop.hom)

/-- **The members of a standard affine covering, read through the product.**  Composing the
`k`-th evaluation of the product of global sections with the map it is a factor of, and then
with the inverse of `AlgebraicGeometry.Scheme.isoSpec` of the target, recovers `g k`. -/
@[reassoc]
lemma specPiEval_comp_specMap_piAppTopHom {n : ℕ} {W : Scheme.{u}} [IsAffine W]
    {A : Fin n → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ W) (k : Fin n) :
    specPiEval (fun j ↦ Γ(Spec (A j), ⊤)) k ≫ Spec.map (piAppTopHom g) ≫ W.isoSpec.inv =
      (Spec (A k)).isoSpec.inv ≫ g k := by
  rw [← Category.assoc, specPiEval, ← Spec.map_comp]
  have h : piAppTopHom g ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun j : Fin n ↦ (Γ(Spec (A j), ⊤) : Type u)) k) =
      (g k).appTop := by
    ext x
    rfl
  rw [h, Scheme.isoSpec_inv_naturality]

/-- **Separatedness for a standard affine covering, over an arbitrary object.**  For a morphism
`φ` from `R₀` to a finite product of rings, a morphism `a : Spec R₀ ⟶ S` and quasi-coherent
modules `M` and `N` on `S`, the presheaf of morphisms is separated for the family obtained by
subdividing `Spec.map φ` along the factors of the product. -/
theorem isSeparatedFor_presheafHom_standardAffine_over {R₀ : CommRingCat.{u}} {n : ℕ}
    {B : Fin n → CommRingCat.{u}} (φ : R₀ ⟶ CommRingCat.of (∀ k : Fin n, (B k : Type u)))
    (hφ : φ.hom.FaithfullyFlat) (a : Spec R₀ ⟶ S) (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presieve.IsSeparatedFor (modulePullbackPseudofunctor.presheafHom M N)
      (overPresieveOn (Over.mk a) (fun k ↦ specPiEval B k ≫ Spec.map φ)) := by
  refine Presieve.isSeparatedFor_of_factorsThru
    (isSheafFor_presheafHom_specMap_over φ hφ a M N).isSeparatedFor ?_
  rintro _ _ ⟨j⟩
  refine ⟨overPresieveOn (Over.mk (Spec.map φ ≫ a)) (specPiEval B),
    (isSheafFor_presheafHom_zariski_over M N (Over.mk (Spec.map φ ≫ a)) (specPiEval B)
      (ofArrows_specPiEval_mem_zariskiPrecoverage B)).isSeparatedFor, ?_⟩
  rintro _ _ ⟨k⟩
  refine ⟨_, ?_, _, Presieve.ofArrows.mk k, ?_⟩
  · exact Over.homMk (𝟙 _) (by simp)
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    simp

/-- **The separatedness half of Stacks 023T for an arbitrary fpqc covering family.**  For
quasi-coherent modules `M` and `N` on `S`, every object `T` of the schemes over `S` and every
fpqc covering family of `T.left`, the presheaf of morphisms is separated for the family read as
a family of morphisms to `T`. -/
theorem isSeparatedFor_presheafHom_fpqc (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (T : Over S) {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ T.left)
    (hu : Presieve.ofArrows U u ∈ Scheme.fpqcPrecoverage.{u} T.left) :
    Presieve.IsSeparatedFor (modulePullbackPseudofunctor.presheafHom M N)
      (overPresieveOn T u) := by
  refine Presieve.isSeparatedFor_of_factorsThru
    (isSheafFor_presheafHom_zariski_over M N T _
      (ofArrows_affineOpens_mem_zariskiPrecoverage T.left)).isSeparatedFor ?_
  rintro Q q ⟨V⟩
  obtain ⟨n, A, g, a, t, hflat, hcov, hopen, hcomm, hff⟩ :=
    exists_standardFpqcCovering_over_affineOpen ⟨ι, U, u⟩ hu V
  have key := isSeparatedFor_presheafHom_standardAffine_over
    (B := fun j ↦ Γ(Spec (A j), ⊤)) (piAppTopHom g) hff
    ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ T.hom) M N
  refine ⟨_, key, ?_⟩
  rintro _ _ ⟨k⟩
  refine ⟨_, ?_, _, Presieve.ofArrows.mk (a k), ?_⟩
  · refine Over.homMk ((Spec (A k)).isoSpec.inv ≫ t k) ?_
    simp only [Over.mk_hom, Category.assoc, specPiEval_comp_specMap_piAppTopHom_assoc]
    rw [← Category.assoc (g k) V.1.ι T.hom, ← hcomm k]
    simp
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    simp only [Over.homMk_left, Category.assoc, specPiEval_comp_specMap_piAppTopHom_assoc]
    rw [← hcomm k]

open Limits in
/-- **The separated refinement the bind criterion asks for, by fpqc base change.**  Let `R` be a
presieve on `T` refined by an fpqc covering family of `T.left`.  Then over every object `Q` of
the schemes over `S` mapping to `T` there is a presieve for which the presheaf of morphisms is
separated and which factors through `R` along the map. -/
theorem exists_isSeparatedFor_factorsThruAlong_fpqc (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] {T : Over S} (R : Presieve T) {ι : Type*}
    {U : ι → Scheme.{u}} (w : ∀ i, U i ⟶ T.left)
    (hw : Presieve.ofArrows U w ∈ Scheme.fpqcPrecoverage.{u} T.left)
    (hfac : (overPresieveOn T w).FactorsThru R) {Q : Over S} (c : Q ⟶ T) :
    ∃ R' : Presieve Q,
      Presieve.IsSeparatedFor (modulePullbackPseudofunctor.presheafHom M N) R' ∧
        R'.FactorsThruAlong R c := by
  have hbc : Presieve.ofArrows (fun i ↦ pullback (w i) c.left)
      (fun i ↦ pullback.snd (w i) c.left) ∈ Scheme.fpqcPrecoverage.{u} Q.left :=
    Precoverage.mem_coverings_of_isPullback w hw c.left _
      (fun i ↦ pullback.fst (w i) c.left)
      (fun i ↦ (IsPullback.of_hasPullback (w i) c.left).flip)
  refine ⟨overPresieveOn Q (fun i ↦ pullback.snd (w i) c.left),
    isSeparatedFor_presheafHom_fpqc M N Q _ hbc, ?_⟩
  rintro _ _ ⟨i⟩
  obtain ⟨W, i', e, he, hcomm⟩ := hfac (Presieve.ofArrows.mk (ι := ι) i)
  have hsq : pullback.fst (w i) c.left ≫ w i ≫ T.hom =
      pullback.snd (w i) c.left ≫ Q.hom := by
    rw [← Category.assoc, pullback.condition, Category.assoc, Over.w c]
  refine ⟨W, (Over.homMk (pullback.fst (w i) c.left) hsq :
    Over.mk (pullback.snd (w i) c.left ≫ Q.hom) ⟶ Over.mk (w i ≫ T.hom)) ≫ i', e, he, ?_⟩
  have h2 : i'.left ≫ e.left = w i := by rw [← Over.comp_left, hcomm]; rfl
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left, Category.assoc, h2]
  exact pullback.condition

/-- **A standard affine covering is an fpqc covering.**  For `φ` faithfully flat into a finite
product of rings, the family obtained by subdividing `Spec.map φ` along the factors of the
product is an fpqc covering family of `Spec R₀`. -/
lemma ofArrows_standardAffine_mem_fpqcPrecoverage {R₀ : CommRingCat.{u}} {n : ℕ}
    (B : Fin n → CommRingCat.{u}) (φ : R₀ ⟶ CommRingCat.of (∀ k : Fin n, (B k : Type u)))
    (hφ : φ.hom.FaithfullyFlat) :
    Presieve.ofArrows (fun p : Σ _ : PUnit.{1}, Fin n ↦ Spec (B p.2))
      (fun p ↦ specPiEval B p.2 ≫ Spec.map φ) ∈ Scheme.fpqcPrecoverage.{u} (Spec R₀) := by
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff φ).mpr hφ
  have hqc : QuasiCompact (Spec.map φ) := quasiCompact_of_compactSpace _
  have hf : Presieve.ofArrows
      (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of (∀ k : Fin n, (B k : Type u))))
      (fun _ ↦ Spec.map φ) ∈ Scheme.fpqcPrecoverage.{u} (Spec R₀) := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @Flat.{u}) hflat
  exact Precoverage.comp_mem_coverings _ hf (fun _ k ↦ specPiEval B k)
    (fun _ ↦ Scheme.zariskiPrecoverage_le_fpqcPrecoverage _
      (ofArrows_specPiEval_mem_zariskiPrecoverage B))

/-- **The sheaf condition for a standard affine covering, over an arbitrary object.**  For `φ`
faithfully flat into a finite product of rings, `a : Spec R₀ ⟶ S` and quasi-coherent `M` and
`N`, the presheaf of morphisms satisfies the sheaf condition for the subdivision of `Spec.map φ`
along the factors of the product, over the object `Over.mk a` of the schemes over `S`. -/
theorem isSheafFor_presheafHom_standardAffine_over {R₀ : CommRingCat.{u}} {n : ℕ}
    (B : Fin n → CommRingCat.{u}) (φ : R₀ ⟶ CommRingCat.of (∀ k : Fin n, (B k : Type u)))
    (hφ : φ.hom.FaithfullyFlat) (a : Spec R₀ ⟶ S) (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      (Presieve.bindArrows
        (fun _ : PUnit.{1} ↦ (Over.homMk (Spec.map φ) :
            Over.mk (Spec.map φ ≫ (Over.mk a).hom) ⟶ Over.mk a))
        (fun _ ↦ overPresieveOn (Over.mk (Spec.map φ ≫ (Over.mk a).hom)) (specPiEval B))) := by
  refine Presieve.isSheafFor_of_bindArrows _ _ _
    (isSheafFor_presheafHom_specMap_over φ hφ a M N)
    (fun _ ↦ isSheafFor_presheafHom_zariski_over M N
      (Over.mk (Spec.map φ ≫ (Over.mk a).hom)) (specPiEval B)
      (ofArrows_specPiEval_mem_zariskiPrecoverage B))
    le_rfl ?_ ?_
  · intro _ Q c
    exact exists_isSeparatedFor_factorsThruAlong_fpqc M N
      (overPresieveOn (Over.mk (Spec.map φ ≫ (Over.mk a).hom)) (specPiEval B))
      (specPiEval B) (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _
        (ofArrows_specPiEval_mem_zariskiPrecoverage B))
      (Presieve.factorsThru_of_le _ _ le_rfl) c
  · exact fun Q h hh ↦ ⟨⊤, Presieve.isSeparatedFor_top _, fun Z g _ ↦ ⟨Q, g, h, hh, rfl⟩⟩

open Limits in
/-- **The fpqc sheaf condition for the presheaf of morphisms of quasi-coherent modules.**  For
every fpqc covering family `f i : X i ⟶ S` and all quasi-coherent modules `M` and `N` on `S`,
the presheaf of morphisms satisfies the sheaf condition for the family read on the terminal
object of the schemes over `S`. -/
theorem isSheafFor_presheafHom_fpqc (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N) (overPresieve f) := by
  classical
  choose n A g aa t hflat hcov hopen hcomm hff using
    fun V : S.affineOpens ↦ exists_standardFpqcCovering_over_affineOpen
      (⟨ι, X, f⟩ : PreZeroHypercover S) hf V
  refine (Presieve.isSheafFor_iff_generate (overPresieve f)).mpr
    (Presieve.isSheafFor_of_bindArrows
      (fun V : S.affineOpens ↦ (Over.homMk (V.1.toScheme.isoSpec.inv ≫ V.1.ι) :
        Over.mk ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ (Over.mk (𝟙 S)).hom) ⟶ Over.mk (𝟙 S)))
      (fun V ↦ Presieve.bindArrows
        (fun _ : PUnit.{1} ↦ (Over.homMk (Spec.map (piAppTopHom (g V))) :
          Over.mk (Spec.map (piAppTopHom (g V)) ≫
            (Over.mk ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ (Over.mk (𝟙 S)).hom)).hom) ⟶
            Over.mk ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ (Over.mk (𝟙 S)).hom)))
        (fun _ ↦ overPresieveOn
          (Over.mk (Spec.map (piAppTopHom (g V)) ≫
            (Over.mk ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ (Over.mk (𝟙 S)).hom)).hom))
          (specPiEval (fun j ↦ Γ(Spec (A V j), ⊤)))))
      _ ?_ ?_ ?_ ?_ ?_)
  · exact isSheafFor_presheafHom_zariski_over M N (Over.mk (𝟙 S))
      (fun V : S.affineOpens ↦ V.1.toScheme.isoSpec.inv ≫ V.1.ι)
      (ofArrows_affineOpens_mem_zariskiPrecoverage S)
  · exact fun V ↦ isSheafFor_presheafHom_standardAffine_over (fun j ↦ Γ(Spec (A V j), ⊤))
      (piAppTopHom (g V)) (hff V)
      ((V.1.toScheme.isoSpec.inv ≫ V.1.ι) ≫ (Over.mk (𝟙 S)).hom) M N
  · rintro Z q ⟨V, -, ⟨-, -, ⟨k⟩, rfl⟩, rfl⟩
    refine ⟨Over.mk (f (aa V k)), ?_, Over.homMk (f (aa V k)),
      Presieve.ofArrows.mk (aa V k), ?_⟩
    · refine Over.homMk ((Spec (A V k)).isoSpec.inv ≫ t V k) ?_
      simp only [Over.mk_hom, Category.assoc, Category.comp_id,
        specPiEval_comp_specMap_piAppTopHom_assoc]
      rw [← hcomm V k]
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc,
        specPiEval_comp_specMap_piAppTopHom_assoc]
      rw [← hcomm V k]
  · intro V Q c
    refine exists_isSeparatedFor_factorsThruAlong_fpqc M N _
      (fun p : Σ _ : PUnit.{1}, Fin (n V) ↦
        specPiEval (fun j ↦ Γ(Spec (A V j), ⊤)) p.2 ≫ Spec.map (piAppTopHom (g V)))
      (ofArrows_standardAffine_mem_fpqcPrecoverage (fun j ↦ Γ(Spec (A V j), ⊤))
        (piAppTopHom (g V)) (hff V)) ?_ c
    rintro _ _ ⟨p⟩
    refine ⟨_, ?_, _, Presieve.bindArrows_comp PUnit.unit (Presieve.ofArrows.mk p.2), ?_⟩
    · exact Over.homMk (𝟙 _) (by simp)
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, Category.id_comp]
  · intro Q h hh
    refine exists_isSeparatedFor_factorsThruAlong_fpqc M N _
      (fun q : Σ V : S.affineOpens, Σ _ : PUnit.{1}, Fin (n V) ↦
        (specPiEval (fun j ↦ Γ(Spec (A q.1 j), ⊤)) q.2.2 ≫
          Spec.map (piAppTopHom (g q.1))) ≫ (q.1.1.toScheme.isoSpec.inv ≫ q.1.1.ι)) ?_ ?_ h
    · exact Precoverage.comp_mem_coverings _
        (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _
          (ofArrows_affineOpens_mem_zariskiPrecoverage S)) _
        (fun V ↦ ofArrows_standardAffine_mem_fpqcPrecoverage (fun j ↦ Γ(Spec (A V j), ⊤))
          (piAppTopHom (g V)) (hff V))
    · rintro _ _ ⟨q⟩
      refine ⟨_, ?_, _, Presieve.bindArrows_comp q.1
        (Presieve.bindArrows_comp PUnit.unit (Presieve.ofArrows.mk q.2.2)), ?_⟩
      · exact Over.homMk (𝟙 _) (by simp)
      · apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left, Category.id_comp]

/-- **Descent of morphisms of quasi-coherent modules along fpqc covering families, with no
hypothesis.**  For every fpqc covering family `f i : X i ⟶ S` and all quasi-coherent modules `M`
and `N` on `S`, pulling morphisms `M ⟶ N` back along the family is a bijection onto the
morphisms of the associated descent data: `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`,
the full-faithfulness half of Stacks 023T. -/
theorem fpqcDescentOfQuasicoherentHoms : FpqcDescentOfQuasicoherentHoms.{u} := by
  intro S I X f hfpqc M N
  have hb : Function.Bijective
      ((modulePullbackPseudofunctor.toDescentData f).map : (M.obj ⟶ N.obj) → _) :=
    (Pseudofunctor.bijective_toDescentData_map_iff
      (F := modulePullbackPseudofunctor) f M.obj N.obj).mpr
      (isSheafFor_presheafHom_fpqc M.obj N.obj f hfpqc)
  have hcomp : Function.Bijective
      ((modulePullbackPseudofunctor.toDescentData f).map ∘
        ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map : (M ⟶ N) → _)) :=
    hb.comp ((ObjectProperty.fullyFaithfulι
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)).map_bijective M N)
  rwa [← ι_comp_toDescentData_map f M N] at hcomp

/-- **The presheaf of morphisms of quasi-coherent modules is an fpqc sheaf, with no
hypothesis.**  `AlgebraicGeometry.isSheaf_presheafHom` with its hypothesis discharged. -/
theorem isSheaf_presheafHom' (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (modulePullbackPseudofunctor.presheafHom M N) :=
  isSheaf_presheafHom fpqcDescentOfQuasicoherentHoms M N

/-- For every fpqc covering family the functor from the quasi-coherent `𝒪_S`-modules to the
descent data with respect to that family is fully faithful. -/
@[stacks 023T "the `moreover` assertion, full faithfulness", sga "1 VIII 1.1" "full faithfulness"]
theorem nonempty_fullyFaithful_canonicalDescentFunctor' {I : Type (u + 1)}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  nonempty_fullyFaithful_of_fpqcDescentOfQuasicoherentHoms fpqcDescentOfQuasicoherentHoms f hfpqc

/-- The pullback-sections presheaf of Stacks 03DS of a quasi-coherent module satisfies the sheaf
condition for every fpqc covering. -/
@[stacks 03DT "fpqc covering"]
theorem quasiCoherentPresheaf_isSheaf_fpqc' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  quasiCoherentPresheaf_isSheaf_fpqc fpqcDescentOfQuasicoherentHoms S F

/-- The pullback-sections presheaf of Stacks 03DS of a quasi-coherent module satisfies the sheaf
condition for every étale covering. -/
@[stacks 03DT "étale covering"]
theorem quasiCoherentPresheaf_isSheaf_etale' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  quasiCoherentPresheaf_isSheaf_etale fpqcDescentOfQuasicoherentHoms S F

/-- The pullback-sections presheaf of Stacks 03DS of a quasi-coherent module satisfies the sheaf
condition for every smooth covering. -/
@[stacks 03DT "smooth covering"]
theorem quasiCoherentPresheaf_isSheaf_smooth' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf ((Scheme.grothendieckTopology (@Smooth)).over S)
      (quasiCoherentPresheafFunctor S F) :=
  quasiCoherentPresheaf_isSheaf_smooth fpqcDescentOfQuasicoherentHoms S F

/-- The pullback-sections presheaf of Stacks 03DS of a quasi-coherent module satisfies the sheaf
condition for every syntomic covering. -/
@[stacks 03DT "syntomic covering"]
theorem quasiCoherentPresheaf_isSheaf_syntomic' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf ((Scheme.grothendieckTopology (@Syntomic)).over S)
      (quasiCoherentPresheafFunctor S F) :=
  quasiCoherentPresheaf_isSheaf_syntomic fpqcDescentOfQuasicoherentHoms S F

/-- The pullback-sections presheaf of Stacks 03DS of a quasi-coherent module satisfies the sheaf
condition for every fppf covering. -/
@[stacks 03DT "fppf covering"]
theorem quasiCoherentPresheaf_isSheaf_fppf' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  quasiCoherentPresheaf_isSheaf_fppf fpqcDescentOfQuasicoherentHoms S F

end AlgebraicGeometry

end

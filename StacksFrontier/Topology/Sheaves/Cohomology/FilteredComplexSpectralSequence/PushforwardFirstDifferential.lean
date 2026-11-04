module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HigherDirectImageSpectralSequence
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.FirstPageConnecting

/-!
# The first differential of the relative spectral sequence of a filtered complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `J` a filtered complex of
`𝒪_X`-modules whose filtration steps have injective terms (a filtered K-injective resolution, in
the application). The spectral sequence of the filtered complex `f_*J`
(`Stacks.Cohomology.FilteredComplex.pushforwardSpectralSequence`) has first page
`E_1^{p, q} = H^{p + q}(f_*gr^pJ)`, and its first differential is the connecting morphism of `f_*`
of the short exact sequence `0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0`.

## Main definitions

* `CochainComplex.Filtered.grShortComplexMapOfMonoIso`: for an additive functor `T` and a
  filtered complex `M` whose filtration steps have injective terms, the short exact sequence
  `gr^{p + 1} ⟶ F^p/F^{p + 2} ⟶ gr^p` of `T(M)` is `T` of that of `M`.
* `CochainComplex.Filtered.mapOfMonoFirstPageIso`: `E_1^{p, q}(T(M)) ≅ H^{p + q}(T(gr^pM))`.
* `Stacks.Cohomology.FilteredComplex.pushforwardFirstPageIso`: the case `T = f_*`.
* `Stacks.Cohomology.FilteredComplex.FilteredKInjectiveResolution.chosen`: the filtered
  K-injective resolution of [Stacks, Tag 0BKI], as a `FilteredKInjectiveResolution`.

## Main results

* `CochainComplex.Filtered.mapOfMono_firstPage_d`: the first differential of the spectral
  sequence of `T(M)` is the connecting morphism of `T` of that short exact sequence.
* `Stacks.Cohomology.FilteredComplex.pushforwardSpectralSequence_d`: the case `T = f_*`.

## References

* [Stacks Project, Tag 0FLL](https://stacks.math.columbia.edu/tag/0FLL)
* [Stacks Project, Tag 012K](https://stacks.math.columbia.edu/tag/012K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

/-! ### An additive functor applied to a filtered complex with injective steps -/

namespace CochainComplex.Filtered

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
  (T : A ⥤ B) [T.Additive]

/-- The isomorphism `Coker(T(f)) ≅ T(Coker f)` of `CochainComplex.cokernelMapIsoOfInjective`
is compatible with the two cokernel projections. -/
@[reassoc (attr := simp)]
lemma π_cokernelMapIsoOfInjective_hom {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [Mono φ] (hK : ∀ n, Injective (K.X n)) :
    cokernel.π ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
        (CochainComplex.cokernelMapIsoOfInjective T φ hK).hom =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (cokernel.π φ) := by
  simp only [CochainComplex.cokernelMapIsoOfInjective, Iso.symm_hom]
  exact IsColimit.comp_coconePointUniqueUpToIso_inv _
    (cokernelIsCokernel ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map φ))
    WalkingParallelPair.one

/-- **The morphism of short exact sequences `gr^{p + 1} ⟶ F^p/F^{p + 2} ⟶ gr^p` induced by a
morphism of filtered complexes.** Its outer components are `gr^{p + 1}φ` and `gr^pφ`
(`grShortComplexMap_τ₁`, `grShortComplexMap_τ₃`). -/
def grShortComplexMap {M N : Filtered A} (φ : M ⟶ N) (p : ℤ) :
    M.grShortComplex p ⟶ N.grShortComplex p where
  τ₁ := cokernel.map (M.succStep (p + 1)) (N.succStep (p + 1)) (φ.natTrans.app _)
    (φ.natTrans.app _) (FilteredObject.step_natTrans_app φ _)
  τ₂ := cokernel.map (M.succStep (p + 1) ≫ M.succStep p) (N.succStep (p + 1) ≫ N.succStep p)
    (φ.natTrans.app _) (φ.natTrans.app _) (by
      rw [Category.assoc, FilteredObject.step_natTrans_app, ← Category.assoc,
        FilteredObject.step_natTrans_app, Category.assoc])
  τ₃ := cokernel.map (M.succStep p) (N.succStep p) (φ.natTrans.app _)
    (φ.natTrans.app _) (FilteredObject.step_natTrans_app φ _)
  comm₁₂ := coequalizer.hom_ext (by
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc, Category.id_comp]
    rw [← Category.assoc, ← Category.assoc, ← FilteredObject.step_natTrans_app φ])
  comm₂₃ := coequalizer.hom_ext (by
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc, Category.id_comp])

/-- The first component of `grShortComplexMap φ p` is `gr^{p + 1} φ`. -/
lemma grShortComplexMap_τ₁ {M N : Filtered A} (φ : M ⟶ N) (p : ℤ) :
    (grShortComplexMap φ p).τ₁ = (FilteredObject.gr (p + 1)).map φ :=
  rfl

/-- The third component of `grShortComplexMap φ p` is `gr^p φ`. -/
lemma grShortComplexMap_τ₃ {M N : Filtered A} (φ : M ⟶ N) (p : ℤ) :
    (grShortComplexMap φ p).τ₃ = (FilteredObject.gr p).map φ :=
  rfl

variable (M : Filtered A) (hM : ∀ p n : ℤ, Injective ((M.filtration.obj (op p)).X n))
  (h : ∀ i, Mono ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map (M.filtration.ι.app i)))

/-- The filtered complex `T(M)`, filtered by the `T(F^pM)`, for `T` preserving the monomorphisms
`F^pM ⟶ M`. -/
abbrev mapComplexOfMono : Filtered B :=
  M.mapOfMono (T.mapHomologicalComplex (ComplexShape.up ℤ)) h

/-- `gr^p T(M) ≅ T(gr^p M)`, when the filtration steps of `M` have injective terms. -/
def grMapOfMonoIso (p : ℤ) :
    (FilteredObject.gr p).obj (mapComplexOfMono T M h) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr p).obj M) :=
  CochainComplex.cokernelMapIsoOfInjective T (M.succStep p) (hM (p + 1))

/-- The isomorphism `grMapOfMonoIso` is compatible with the projections `T(F^pM) ⟶ gr^p T(M)` and
`T(F^pM) ⟶ T(gr^p M)`. -/
@[reassoc]
lemma π_grMapOfMonoIso_hom (p : ℤ) :
    cokernel.π ((mapComplexOfMono T M h).succStep p) ≫
        (grMapOfMonoIso T M hM h p).hom =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (cokernel.π (M.succStep p)) :=
  π_cokernelMapIsoOfInjective_hom T (M.succStep p) (hM (p + 1))

/-- `F^p/F^{p + 2}` of `T(M)` is `T` of `F^p/F^{p + 2}` of `M`, when the filtration steps of `M`
have injective terms. -/
def twoStepMapOfMonoIso (p : ℤ) :
    ((mapComplexOfMono T M h).grShortComplex p).X₂ ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj (M.grShortComplex p).X₂ :=
  cokernel.mapIso ((mapComplexOfMono T M h).succStep (p + 1) ≫
      (mapComplexOfMono T M h).succStep p) ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (M.succStep (p + 1) ≫ M.succStep p)) (Iso.refl _) (Iso.refl _)
      (show ((mapComplexOfMono T M h).succStep (p + 1) ≫ (mapComplexOfMono T M h).succStep p) ≫
          𝟙 _ = 𝟙 _ ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (M.succStep (p + 1) ≫ M.succStep p) by
        rw [Category.comp_id, Category.id_comp, Functor.map_comp]; rfl) ≪≫
    CochainComplex.cokernelMapIsoOfInjective T (M.succStep (p + 1) ≫ M.succStep p)
      (hM (p + 1 + 1))

include hM in
/-- The isomorphism `twoStepMapOfMonoIso` is compatible with the projections from `T(F^pM)` to
`F^p/F^{p + 2}` of `T(M)` and to `T(F^pM/F^{p + 2}M)`. -/
@[reassoc]
lemma π_twoStepMapOfMonoIso_hom (p : ℤ) :
    cokernel.π ((mapComplexOfMono T M h).succStep (p + 1) ≫
        (mapComplexOfMono T M h).succStep p) ≫
        (twoStepMapOfMonoIso T M hM h p).hom =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (cokernel.π (M.succStep (p + 1) ≫ M.succStep p)) :=
  (cokernel.π_desc_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans ((Category.id_comp _).trans
    (π_cokernelMapIsoOfInjective_hom T (M.succStep (p + 1) ≫ M.succStep p) (hM (p + 1 + 1)))))

/-- **The short exact sequence `gr^{p + 1} ⟶ F^p/F^{p + 2} ⟶ gr^p` of `T(M)` is `T` of that of
`M`**, when the filtration steps of `M` have injective terms. -/
def grShortComplexMapOfMonoIso (p : ℤ) :
    (mapComplexOfMono T M h).grShortComplex p ≅
      (M.grShortComplex p).map (T.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  ShortComplex.isoMk (grMapOfMonoIso T M hM h (p + 1)) (twoStepMapOfMonoIso T M hM h p)
    (grMapOfMonoIso T M hM h p)
    (by
      have h₁ : cokernel.π (M.succStep (p + 1)) ≫ (M.grShortComplex p).f =
          M.succStep p ≫ cokernel.π (M.succStep (p + 1) ≫ M.succStep p) :=
        cokernel.π_desc _ _ _
      have h₂ : cokernel.π ((mapComplexOfMono T M h).succStep (p + 1)) ≫
          ((mapComplexOfMono T M h).grShortComplex p).f =
          (mapComplexOfMono T M h).succStep p ≫ cokernel.π
            ((mapComplexOfMono T M h).succStep (p + 1) ≫ (mapComplexOfMono T M h).succStep p) :=
        cokernel.π_desc _ _ _
      refine (cancel_epi (cokernel.π ((mapComplexOfMono T M h).succStep (p + 1)))).1 ?_
      have h₃ : cokernel.π ((mapComplexOfMono T M h).succStep (p + 1)) ≫
          ((mapComplexOfMono T M h).grShortComplex p).f ≫ (twoStepMapOfMonoIso T M hM h p).hom =
          (mapComplexOfMono T M h).succStep p ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (cokernel.π (M.succStep (p + 1) ≫ M.succStep p)) := by
        rw [← Category.assoc, h₂, Category.assoc, π_twoStepMapOfMonoIso_hom]
      refine (π_grMapOfMonoIso_hom_assoc T M hM h (p + 1) _).trans ?_
      refine ((Functor.map_comp _ _ _).symm.trans ((congrArg _ h₁).trans
        (Functor.map_comp _ _ _))).trans h₃.symm)
    (by
      have h₁ : cokernel.π (M.succStep (p + 1) ≫ M.succStep p) ≫ (M.grShortComplex p).g =
          cokernel.π (M.succStep p) :=
        (cokernel.π_desc _ _ _).trans (Category.id_comp _)
      have h₂ : cokernel.π ((mapComplexOfMono T M h).succStep (p + 1) ≫
            (mapComplexOfMono T M h).succStep p) ≫
          ((mapComplexOfMono T M h).grShortComplex p).g =
          cokernel.π ((mapComplexOfMono T M h).succStep p) :=
        (cokernel.π_desc _ _ _).trans (Category.id_comp _)
      refine (cancel_epi (cokernel.π ((mapComplexOfMono T M h).succStep (p + 1) ≫
          (mapComplexOfMono T M h).succStep p))).1 ?_
      refine (π_twoStepMapOfMonoIso_hom_assoc T M hM h p _).trans ?_
      refine ((Functor.map_comp _ _ _).symm.trans (congrArg _ h₁)).trans ?_
      have h₃ : cokernel.π ((mapComplexOfMono T M h).succStep (p + 1) ≫
            (mapComplexOfMono T M h).succStep p) ≫
          ((mapComplexOfMono T M h).grShortComplex p).g ≫ (grMapOfMonoIso T M hM h p).hom =
          (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (cokernel.π (M.succStep p)) := by
        rw [← Category.assoc, h₂, π_grMapOfMonoIso_hom]
      exact h₃.symm)

include hM h in
/-- `T` of the short exact sequence `gr^{p + 1}M ⟶ F^pM/F^{p + 2}M ⟶ gr^pM` is short exact, when
the filtration steps of `M` have injective terms. -/
lemma shortExact_map_grShortComplex (p : ℤ) :
    ((M.grShortComplex p).map (T.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact :=
  ShortComplex.shortExact_of_iso (grShortComplexMapOfMonoIso T M hM h p)
    (grShortComplex_shortExact _ p)

/-- The first page of the spectral sequence of `T(M)` is the cohomology of `T(gr^pM)`. -/
def mapOfMonoFirstPageIso (p q n : ℤ) (hn : n = p + q) :
    ((spectralSequenceFunctor.obj
        (mapComplexOfMono T M h)).page 1 (by omega)).X
        (p, q) ≅
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr p).obj M)).homology
        n :=
  firstPageIso _ p q n hn ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (grMapOfMonoIso T M hM h p)

/-- **The first differential of the spectral sequence of `T(M)`** is the connecting morphism, in
the cohomology of `T` of the graded pieces, of `T` of the short exact sequence
`0 ⟶ gr^{p + 1}M ⟶ F^pM/F^{p + 2}M ⟶ gr^pM ⟶ 0`, when the filtration steps of `M` have
injective terms. -/
theorem mapOfMono_firstPage_d (p q n n' : ℤ) (hn : n = p + q) (hn' : n' = n + 1) :
    ((spectralSequenceFunctor.obj
        (mapComplexOfMono T M h)).page 1 (by omega)).d
        (p, q) (p + 1, q) =
      (mapOfMonoFirstPageIso T M hM h p q n hn).hom ≫
        (shortExact_map_grShortComplex T M hM h p).δ n n' (by simp [hn']) ≫
          (mapOfMonoFirstPageIso T M hM h (p + 1) q n' (by omega)).inv := by
  rw [firstPage_d _ p q n n' hn hn']
  have hδ : HomologicalComplex.homologyMap (grMapOfMonoIso T M hM h p).hom n ≫
      (shortExact_map_grShortComplex T M hM h p).δ n n' (by simp [hn']) =
      (grShortComplex_shortExact _ p).δ n n' (by simp [hn']) ≫
        HomologicalComplex.homologyMap (grMapOfMonoIso T M hM h (p + 1)).hom n' :=
    (HomologicalComplex.HomologySequence.δ_naturality (grShortComplexMapOfMonoIso T M hM h p).hom
      (grShortComplex_shortExact _ p) (shortExact_map_grShortComplex T M hM h p) n n'
      (by simp [hn'])).symm
  show _ = (((mapComplexOfMono T M h).firstPageIso p q n hn).hom ≫
      HomologicalComplex.homologyMap (grMapOfMonoIso T M hM h p).hom n) ≫
    (shortExact_map_grShortComplex T M hM h p).δ n n' (by simp [hn']) ≫
      HomologicalComplex.homologyMap (grMapOfMonoIso T M hM h (p + 1)).inv n' ≫
        ((mapComplexOfMono T M h).firstPageIso (p + 1) q n' (by omega)).inv
  rw [Category.assoc, reassoc_of% hδ, ← HomologicalComplex.homologyMap_comp_assoc, Iso.hom_inv_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]

end CochainComplex.Filtered

/-! ### The first differential of `f_*` of a filtered complex with injective steps -/

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] modulePushforward_isRightAdjoint

/-- **A chosen filtered K-injective resolution** of a filtered complex of `𝒪_X`-modules: the one
produced by [Stacks, Tag 0BKI] (`Stacks.Injectives.exists_filtered_quasiIso_isKInjective`). -/
def FilteredKInjectiveResolution.chosen (X : RingedSpace.{u, u})
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    FilteredKInjectiveResolution X K :=
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  have H := Stacks.Injectives.exists_filtered_quasiIso_isKInjective K
  { obj := H.choose
    map := H.choose_spec.choose
    quasiIso := H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1
    quasiIso_step := H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.1
    quasiIso_gr := fun p => H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2 p (p + 1) (by omega)
    injective_step := H.choose_spec.choose_spec.2.1
    isKInjective := H.choose_spec.choose_spec.2.2.2.2.1
    isKInjective_step := H.choose_spec.choose_spec.2.2.2.2.2.1
    isKInjective_gr := fun p => H.choose_spec.choose_spec.2.2.2.2.2.2.2.1 p (p + 1) (by omega) }

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
  (hJ : ∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n))

/-- The first page of the spectral sequence of `f_*J` is the cohomology of `f_*gr^pJ`, when the
filtration steps of `J` have injective terms. -/
def pushforwardFirstPageIso (p q n : ℤ) (hn : n = p + q) :
    ((pushforwardSpectralSequence f J).page 1 (by omega)).X (p, q) ≅
      ((pushforwardComplexFunctor f).obj ((FilteredObject.gr p).obj J)).homology n :=
  CochainComplex.Filtered.mapOfMonoFirstPageIso (modulePushforward f) J hJ
    (fun _ => inferInstance) p q n hn

include hJ in
/-- `f_*` of the short exact sequence `gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ` is short exact, when
the filtration steps of `J` have injective terms. -/
lemma shortExact_pushforward_grShortComplex (p : ℤ) :
    ((J.grShortComplex p).map (pushforwardComplexFunctor f)).ShortExact :=
  CochainComplex.Filtered.shortExact_map_grShortComplex (modulePushforward f) J hJ
    (fun _ => inferInstance) p

/-- **The first differential of the spectral sequence of `f_*J`** is the connecting morphism, in
the cohomology of `f_*` of the graded pieces, of `f_*` of the short exact sequence
`0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0`, when the filtration steps of `J` have
injective terms. -/
theorem pushforwardSpectralSequence_d (p q n n' : ℤ) (hn : n = p + q) (hn' : n' = n + 1) :
    ((pushforwardSpectralSequence f J).page 1 (by omega)).d (p, q) (p + 1, q) =
      (pushforwardFirstPageIso f J hJ p q n hn).hom ≫
        (shortExact_pushforward_grShortComplex f J hJ p).δ n n' (by simp [hn']) ≫
          (pushforwardFirstPageIso f J hJ (p + 1) q n' (by omega)).inv :=
  CochainComplex.Filtered.mapOfMono_firstPage_d (modulePushforward f) J hJ
    (fun _ => inferInstance) p q n n' hn hn'

end Stacks.Cohomology.FilteredComplex

end

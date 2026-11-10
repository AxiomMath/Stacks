module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalCompatibility

/-!
# `H^{-1}` of the base change map of `NL`, reduced to the polynomial presentations and to stalks

Let `i : X ⟶ P`, `i' : X' ⟶ P'` be immersions, `h : P ⟶ Y`, `h' : P' ⟶ Y'` formally smooth, and
`i' ≫ p = g' ≫ i` a commutative square.  By [Stacks Project, Tag 0FV4] the cohomology sheaves
`H^{-1}((g')^*NL_{X/Y})` and `H^{-1}(NL_{X'/Y'})` are identified with the kernels of the pulled
back first arrow `(g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y}` and of the first arrow
`𝒞_{X'/P'} ⟶ i'^*Ω_{P'/Y'}` of the conormal sequences of [Stacks Project, Tag 01UZ]
(`Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso` and
`Stacks.NaiveCotangentPulledImmersion.naiveCotangentHomologyNegOneIso`).  The proof of
[Stacks Project, Tag 0FV9] needs that, through these identifications, the map induced on
`H^{-1}` by the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of [Stacks Project, Tag 0FV5] is
the restriction of the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of [Stacks Project, Tag 01R4].

Both identifications are built from zig-zags of chain maps through the naive cotangent complex
of the polynomial presentation of `𝒪_X` on the sections of `i⁻¹𝒪_P` (respectively of `𝒪_{X'}`
on the sections of `i'⁻¹𝒪_{P'}`), in which the arrow towards `NL` is inverted on `H^{-1}`.  This
file removes the two identifications from the statement and reduces what is left to a statement
about stalks.

* `homologyMap_negOne_comp_eq_iff` rewrites the compatibility as an equation of maps out of
  `H^{-1}` of the pulled-back polynomial presentation of `𝒪_X`, in which the identification for
  `X'/Y'` appears as the inverse of the map induced on `H^{-1}` by the polynomial presentation of
  `𝒪_{X'}`, followed by its comparison with `𝒞_{X'/P'}` in degree `-1`.
* `homologyMap_inv_homologyNegOneι_eq_of_stalk` proves an equation of exactly that shape from
  the existence, at every point, of a morphism of the stalks of the degree `-1` terms compatible
  with the differentials and with the two pairs of maps.  It is the sheaf-theoretic half of the
  homotopy-invariance argument: on stalks the two complexes are naive cotangent complexes of
  extensions, and the morphism is the one induced by a morphism of extensions.
* The stalk of the pullback of a sheaf of modules is computed on germs of unit sections
  (`stalkTwoStepPullbackIso_inv_app_unit`), which determine maps out of it
  (`stalkTwoStepPullback_hom_ext`) and through which such maps are constructed from semilinear
  maps out of the stalk downstairs (`stalkTwoStepPullbackDesc`).

## Main definitions

* `Stacks.NaiveCotangentPulledImmersion.homologyNegOneι`: the inclusion of `H^{-1}` into the
  degree `-1` term of a complex with nothing in degree `-2`.
* `Stacks.NaiveCotangentPulledImmersion.presentationToNaiveCotangent`: the comparison of the
  polynomial presentation with `NL_{X/Y}`.
* `Stacks.NaiveCotangentPulledImmersion.stalkTwoStepPullbackDesc`: the map out of the stalk of a
  pullback induced by a semilinear map out of the stalk downstairs.

## Main results

* `Stacks.NaiveCotangentPulledImmersion.homologyMap_homologyNegOneι`: the inclusion of `H^{-1}`
  is natural.
* `Stacks.NaiveCotangentPulledImmersion.naiveCotangentHomologyNegOneIso_hom_ι` and
  `Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso_trans_hom_ι`: the two
  identifications of [Stacks Project, Tag 0FV4], followed by the inclusion of the kernel.
* `Stacks.NaiveCotangentPulledImmersion.homologyMap_negOne_comp_eq_iff`: the reduction to the
  polynomial presentations.
* `Stacks.NaiveCotangentPulledImmersion.hom_ext_of_stalkFunctor_map` and
  `Stacks.NaiveCotangentPulledImmersion.homologyMap_inv_homologyNegOneι_eq_of_stalk`: the
  reduction to stalks.
* `Stacks.NaiveCotangentPulledImmersion.stalkModulePullbackFunctorIso_inv_app_unit` and
  `Stacks.NaiveCotangentPulledImmersion.stalkTwoStepPullbackIso_inv_app_unit`: the stalk of a
  pullback on germs of unit sections ([Stacks Project, Tag 0098], elementwise).

## Implementation notes

The two spellings of the category of sheaves of `𝒪_X`-modules, `AlgebraicGeometry.Scheme.Modules`
and `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_X)`, carry distinct category
instances, so the bookkeeping of `homologyMap_negOne_comp_eq_iff` is done once in a bare category
(`comp_eq_iff_of_comp_eq`) and applied with `exact`.  For the same reason the equation
`f = i ≫ h` is not substituted: the statements are made for `i ≫ h` itself.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentPulledImmersion

section HomologyNegOne

universe w₁ w₂

variable {C : Type w₂} [Category.{w₁} C] [Abelian C]

omit [Abelian C] in
/-- For a short complex with zero first map, the inverse of the projection to homology followed
by the identification of the cycles with the kernel is the inclusion of the cycles. -/
theorem homologyπ_asIsoHomologyπ_symm_trans_ι [HasZeroMorphisms C] (S : ShortComplex C)
    [S.HasHomology] [HasKernel S.g] (hf : S.f = 0) :
    S.homologyπ ≫ ((S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel).hom ≫ kernel.ι S.g =
      S.iCycles := by
  simp

/-- The identification of `H^{-1}` with the kernel of the differential, read on cycles: it is
the inclusion of the cycles. -/
@[reassoc]
theorem homologyπ_homologyNegOneIsoKernel_hom_ι (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    M.homologyπ (-1) ≫ (homologyNegOneIsoKernel M h).hom ≫ kernel.ι (M.d (-1) 0) =
      M.iCycles (-1) := by
  simp only [homologyNegOneIsoKernel, Iso.trans_hom, Category.assoc,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, Iso.symm_hom,
    ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc, ShortComplex.cyclesIsoKernel_hom]
  exact (congrArg (fun t => _ ≫ t)
    (kernel.lift_ι (HomologicalComplex.sc' M (-2) (-1) 0).g _ _)).trans
    (HomologicalComplex.cyclesIsoSc'_hom_iCycles M (-2) (-1) 0 (by simp) (by simp))

/-- The inclusion of the kernel of a morphism conjugated by two isomorphisms, read through
`kernelConjIso`. -/
@[reassoc]
theorem kernelConjIso_hom_ι {A A' B B' : C} (e₁ : A ≅ A') (f : A' ⟶ B') (e₀ : B ≅ B') :
    (kernelConjIso e₁ f e₀).hom ≫ kernel.ι f = kernel.ι (e₁.hom ≫ f ≫ e₀.inv) ≫ e₁.hom := by
  simp [kernelConjIso, kernelIsIsoComp, kernelCompMono]

/-- The inclusion of `H^{-1}` into the degree `-1` term, for a complex with nothing in degree
`-2`. -/
def homologyNegOneι (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    M.homology (-1) ⟶ M.X (-1) :=
  (homologyNegOneIsoKernel M h).hom ≫ kernel.ι (M.d (-1) 0)

/-- On cycles, the inclusion of `H^{-1}` is the inclusion of the cycles. -/
@[reassoc]
theorem homologyπ_homologyNegOneι (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    M.homologyπ (-1) ≫ homologyNegOneι M h = M.iCycles (-1) :=
  homologyπ_homologyNegOneIsoKernel_hom_ι M h

/-- **The inclusion of `H^{-1}` is natural.** -/
@[reassoc]
theorem homologyMap_homologyNegOneι {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (hK : IsZero (K.X (-2))) (hL : IsZero (L.X (-2))) :
    HomologicalComplex.homologyMap φ (-1) ≫ homologyNegOneι L hL =
      homologyNegOneι K hK ≫ φ.f (-1) := by
  refine (cancel_epi (K.homologyπ (-1))).1 ?_
  rw [HomologicalComplex.homologyπ_naturality_assoc, homologyπ_homologyNegOneι,
    homologyπ_homologyNegOneι_assoc, HomologicalComplex.cyclesMap_i]

/-- The inclusion of `H^{-1}` into the degree `-1` term is a monomorphism. -/
instance mono_homologyNegOneι (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    Mono (homologyNegOneι M h) := by
  unfold homologyNegOneι
  infer_instance

/-- The inclusion of `H^{-1}` is a kernel of the differential. -/
theorem exact_homologyNegOneι (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    (ShortComplex.mk (homologyNegOneι M h) (M.d (-1) 0) (by simp [homologyNegOneι])).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (ShortComplex.exact_kernel (M.d (-1) 0))
  exact ShortComplex.isoMk (homologyNegOneIsoKernel M h).symm (Iso.refl _) (Iso.refl _)
    (by simp [homologyNegOneι]) (by simp)

/-- **An identification of `H^{-1}` built from a zig-zag, followed by the inclusion of the
kernel.**  Let `s : N ≅ N₂`, `q : M ⟶ N₂` inducing an isomorphism on `H^{-1}` and `t : M ⟶ T`,
with `M` and `T` vanishing in degree `-2` and the differential of `T` conjugate to `δ`.  The
identification of `H^{-1}(N)` with `Ker δ` made of `s`, the inverse of `H^{-1}(q)`, `H^{-1}(t)`
and the kernel of the differential of `T` is, followed by the inclusion of `Ker δ`, the inverse
of `H^{-1}(q ≫ s⁻¹)` followed by the inclusion of `H^{-1}(M)` and `t` in degree `-1`. -/
theorem zigzagHomologyNegOneIso_hom_ι {N N₂ M T : CochainComplex C ℤ} (s : N ≅ N₂) (q : M ⟶ N₂)
    (t : M ⟶ T) (hq : IsIso (HomologicalComplex.homologyMap q (-1)))
    (ht : IsIso (HomologicalComplex.homologyMap t (-1)))
    (hqs : IsIso (HomologicalComplex.homologyMap (q ≫ s.inv) (-1)))
    (hM : IsZero (M.X (-2))) (hT : IsZero (T.X (-2))) {A B : C} (e₁ : T.X (-1) ≅ A)
    (δ : A ⟶ B) (e₀ : T.X 0 ≅ B) (hd : T.d (-1) 0 = e₁.hom ≫ δ ≫ e₀.inv)
    (e : N.homology (-1) = N.homology (-1)) :
    (eqToIso e ≪≫ (HomologicalComplex.homologyFunctor _ _ (-1)).mapIso s ≪≫
        (@asIso _ _ _ _ (HomologicalComplex.homologyMap q (-1)) hq).symm ≪≫
        @asIso _ _ _ _ (HomologicalComplex.homologyMap t (-1)) ht ≪≫
        homologyNegOneIsoKernel T hT ≪≫ kernelIsoOfEq hd ≪≫ kernelConjIso e₁ δ e₀).hom ≫
        kernel.ι δ =
      @inv _ _ _ _ (HomologicalComplex.homologyMap (q ≫ s.inv) (-1)) hqs ≫
        homologyNegOneι M hM ≫ t.f (-1) ≫ e₁.hom := by
  have hinv : @inv _ _ _ _ (HomologicalComplex.homologyMap (q ≫ s.inv) (-1)) hqs =
      HomologicalComplex.homologyMap s.hom (-1) ≫
        @inv _ _ _ _ (HomologicalComplex.homologyMap q (-1)) hq := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← Category.assoc
      (HomologicalComplex.homologyMap s.inv (-1)), ← HomologicalComplex.homologyMap_comp,
      Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp, IsIso.hom_inv_id]
  rw [hinv]
  change (eqToHom e ≫ HomologicalComplex.homologyMap s.hom (-1) ≫
      (@inv _ _ _ _ (HomologicalComplex.homologyMap q (-1)) hq ≫
        (HomologicalComplex.homologyMap t (-1) ≫ ((homologyNegOneIsoKernel T hT).hom ≫
          ((kernelIsoOfEq hd).hom ≫ (kernelConjIso e₁ δ e₀).hom))))) ≫ kernel.ι δ = _
  rw [eqToHom_refl, Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, kernelConjIso_hom_ι, kernelIsoOfEq_hom_comp_ι_assoc,
    ← Category.assoc (homologyNegOneIsoKernel T hT).hom, ← homologyNegOneι,
    homologyMap_homologyNegOneι_assoc t hM hT, Category.assoc]

/-- `zigzagHomologyNegOneIso_hom_ι` followed by a second conjugation of the kernel. -/
theorem zigzagHomologyNegOneIso_trans_hom_ι {N N₂ M T : CochainComplex C ℤ} (s : N ≅ N₂)
    (q : M ⟶ N₂) (t : M ⟶ T) (hq : IsIso (HomologicalComplex.homologyMap q (-1)))
    (ht : IsIso (HomologicalComplex.homologyMap t (-1)))
    (hqs : IsIso (HomologicalComplex.homologyMap (q ≫ s.inv) (-1)))
    (hM : IsZero (M.X (-2))) (hT : IsZero (T.X (-2))) {A B A' B' : C} (e₁ : T.X (-1) ≅ A)
    (δ : A ⟶ B) (e₀ : T.X 0 ≅ B) (hd : T.d (-1) 0 = e₁.hom ≫ δ ≫ e₀.inv)
    (e₁' : A ≅ A') (δ' : A' ⟶ B') (e₀' : B ≅ B') (hd' : δ = e₁'.hom ≫ δ' ≫ e₀'.inv)
    (e : N.homology (-1) = N.homology (-1)) :
    ((eqToIso e ≪≫ (HomologicalComplex.homologyFunctor _ _ (-1)).mapIso s ≪≫
        (@asIso _ _ _ _ (HomologicalComplex.homologyMap q (-1)) hq).symm ≪≫
        @asIso _ _ _ _ (HomologicalComplex.homologyMap t (-1)) ht ≪≫
        homologyNegOneIsoKernel T hT ≪≫ kernelIsoOfEq hd ≪≫ kernelConjIso e₁ δ e₀) ≪≫
        kernelIsoOfEq hd' ≪≫ kernelConjIso e₁' δ' e₀').hom ≫ kernel.ι δ' =
      @inv _ _ _ _ (HomologicalComplex.homologyMap (q ≫ s.inv) (-1)) hqs ≫
        homologyNegOneι M hM ≫ t.f (-1) ≫ e₁.hom ≫ e₁'.hom := by
  change (_ ≫ (_ ≫ _)) ≫ kernel.ι δ' = _
  rw [Category.assoc, Category.assoc, kernelConjIso_hom_ι, kernelIsoOfEq_hom_comp_ι_assoc,
    ← Category.assoc, zigzagHomologyNegOneIso_hom_ι s q t hq ht hqs hM hT e₁ δ e₀ hd e]
  simp only [Category.assoc]

omit [Abelian C] in
/-- The bookkeeping of `homologyMap_negOne_comp_eq_iff`, in a bare category. -/
theorem comp_eq_iff_of_comp_eq {HQ HN HL HM K K' QX QX' E E' D : C} (ρ : HQ ⟶ HN) [IsIso ρ]
    (A : HN ≅ K) (ιK : K ⟶ E) (ιQ : HQ ⟶ QX) (F : QX ⟶ E)
    (hA : A.hom ≫ ιK = inv ρ ≫ ιQ ≫ F) (b : HN ⟶ HL) (B : HL ≅ K') (ιK' : K' ⟶ E')
    (q : HM ⟶ HL) [IsIso q] (ιM : HM ⟶ QX') (G : QX' ⟶ E') (br : D ≅ E')
    (hB : B.hom ≫ ιK' = inv q ≫ ιM ≫ G) (c : E ⟶ D) :
    A.inv ≫ b ≫ B.hom ≫ ιK' = ιK ≫ c ≫ br.hom ↔
      (ρ ≫ b) ≫ inv q ≫ ιM ≫ G ≫ br.inv = ιQ ≫ F ≫ c := by
  rw [hB]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have H2 := congrArg (fun t => ρ ≫ A.hom ≫ t ≫ br.inv) H
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at H2
    rw [Category.assoc, H2, ← Category.assoc A.hom, hA]
    simp
  · have H4 : ρ ≫ b ≫ inv q ≫ ιM ≫ G = ιQ ≫ F ≫ c ≫ br.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (· ≫ br.hom) H
    rw [← cancel_epi (ρ ≫ A.hom)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [H4, ← Category.assoc A.hom, hA]
    simp

/-- A quasi-isomorphism induces an isomorphism on `H^{-1}`. -/
private theorem isIso_homologyMap_negOne_of_quasiIso {K L : CochainComplex C ℤ} {φ : K ⟶ L}
    (hφ : QuasiIso φ) : IsIso (HomologicalComplex.homologyMap φ (-1)) :=
  (quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp (hφ.quasiIsoAt (-1))

end HomologyNegOne

section Stalkwise

open AlgebraicGeometry.SheafOfModules (stalkFunctor stalkMap_germ exact_iff_stalkFunctor_map_exact
  mono_iff_injective_stalkMap)

variable {T : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}

/-- **Morphisms of sheaves of modules on a space agree as soon as they agree on all stalks.** -/
theorem hom_ext_of_stalkFunctor_map {M N : _root_.SheafOfModules.{u} O} {a b : M ⟶ N}
    (hab : ∀ x : T, (stalkFunctor O x).map a = (stalkFunctor O x).map b) : a = b := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext s
  refine TopCat.Presheaf.section_ext (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} T)
    U.unop _ _ fun x hx => ?_
  have e := congrArg (fun φ => φ.hom ((TopCat.Presheaf.germ M.val.presheaf U.unop x hx).hom s))
    (hab x)
  exact (stalkMap_germ O x a U.unop hx s).symm.trans (e.trans (stalkMap_germ O x b U.unop hx s))

variable {K L M : CochainComplex (_root_.SheafOfModules.{u} O) ℤ}

/-- **A map out of `H^{-1}` through the inverse of an isomorphism on `H^{-1}`, tested on
stalks.**  Let `Ψ : K ⟶ L` and `h : M ⟶ L` be morphisms of complexes of sheaves of modules
with nothing in degree `-2`, `h` inducing an isomorphism on `H^{-1}`, and let `k` and `f` be maps
out of the degree `-1` terms of `M` and `K` to a common target.  If at every point there is a
morphism of the stalks of the degree `-1` terms, compatible with the differentials through some
morphism of the degree `0` terms, which carries the stalk of `Ψ` to the stalk of `h` and the stalk
of `f` to the stalk of `k`, then `H^{-1}(Ψ) ≫ H^{-1}(h)⁻¹`, followed by the inclusion of
`H^{-1}(M)` and `k`, is the inclusion of `H^{-1}(K)` followed by `f`. -/
theorem homologyMap_inv_homologyNegOneι_eq_of_stalk (hK : IsZero (K.X (-2)))
    (hL : IsZero (L.X (-2))) (hM : IsZero (M.X (-2))) (Ψ : K ⟶ L) (hh : M ⟶ L)
    [IsIso (HomologicalComplex.homologyMap hh (-1))] {N : _root_.SheafOfModules.{u} O}
    (k : M.X (-1) ⟶ N) (f : K.X (-1) ⟶ N)
    (hloc : ∀ x : T, ∃ (μ₁ : (stalkFunctor O x).obj (K.X (-1)) ⟶ (stalkFunctor O x).obj (M.X (-1)))
      (μ₀ : (stalkFunctor O x).obj (K.X 0) ⟶ (stalkFunctor O x).obj (M.X 0)),
      μ₁ ≫ (stalkFunctor O x).map (M.d (-1) 0) = (stalkFunctor O x).map (K.d (-1) 0) ≫ μ₀ ∧
      μ₁ ≫ (stalkFunctor O x).map (hh.f (-1)) = (stalkFunctor O x).map (Ψ.f (-1)) ∧
      μ₁ ≫ (stalkFunctor O x).map k = (stalkFunctor O x).map f) :
    HomologicalComplex.homologyMap Ψ (-1) ≫ inv (HomologicalComplex.homologyMap hh (-1)) ≫
        homologyNegOneι M hM ≫ k =
      homologyNegOneι K hK ≫ f := by
  refine hom_ext_of_stalkFunctor_map fun x => ?_
  obtain ⟨μ₁, μ₀, hd, hΨ, hf⟩ := hloc x
  let S := stalkFunctor O x
  change S.map _ = S.map _
  ext ξ
  have exM := (ShortComplex.moduleCat_exact_iff _).1
    ((exact_iff_stalkFunctor_map_exact _).1 (exact_homologyNegOneι M hM) x)
  have injL := (mono_iff_injective_stalkMap (homologyNegOneι L hL)).1 inferInstance x
  set m := (S.map (homologyNegOneι K hK)).hom ξ with hm
  have hmd : (S.map (K.d (-1) 0)).hom m = 0 := by
    have h0 : homologyNegOneι K hK ≫ K.d (-1) 0 = 0 := by simp [homologyNegOneι]
    simpa only [S.map_comp, S.map_zero, ModuleCat.hom_comp, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply] using congrArg (fun φ => (S.map φ).hom ξ) h0
  obtain ⟨η, hη⟩ := exM (μ₁.hom m) (by
    change (μ₁ ≫ S.map (M.d (-1) 0)).hom m = 0
    rw [hd, ModuleCat.comp_apply, hmd, map_zero])
  change (S.map (homologyNegOneι M hM)).hom η = μ₁.hom m at hη
  have hηξ : (S.map (HomologicalComplex.homologyMap hh (-1))).hom η =
      (S.map (HomologicalComplex.homologyMap Ψ (-1))).hom ξ := by
    refine injL ?_
    change (S.map (HomologicalComplex.homologyMap hh (-1)) ≫ S.map (homologyNegOneι L hL)).hom η =
      (S.map (HomologicalComplex.homologyMap Ψ (-1)) ≫ S.map (homologyNegOneι L hL)).hom ξ
    rw [← S.map_comp, ← S.map_comp, homologyMap_homologyNegOneι hh hM hL,
      homologyMap_homologyNegOneι Ψ hK hL, S.map_comp, S.map_comp, ModuleCat.comp_apply,
      ModuleCat.comp_apply, hη, ← hm, ← ModuleCat.comp_apply, hΨ]
  have hinv : (S.map (inv (HomologicalComplex.homologyMap hh (-1)))).hom
      ((S.map (HomologicalComplex.homologyMap Ψ (-1))).hom ξ) = η := by
    rw [← hηξ, ← ModuleCat.comp_apply, ← S.map_comp, IsIso.hom_inv_id, S.map_id]
    rfl
  simp only [S.map_comp, ModuleCat.comp_apply]
  rw [hinv, hη, ← hm, ← ModuleCat.comp_apply, hf]

end Stalkwise

section PullbackStalk

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- **The stalk of a pullback on the germ of a unit section** (Stacks 0098, elementwise).  The
identification `(f^*M)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} M_{f(x)}` of
`Stacks.RingedSpace.stalkModulePullbackFunctorIso` carries `1 ⊗ s_{f(x)}`, for `s` a section of
`M` over an open `U ∋ f(x)`, to the germ at `x` of the image of `s` under the unit `M ⟶ f_*f^*M`.
The element `1 ⊗ s_{f(x)}` is written as the value of the unit of extension and restriction of
scalars. -/
theorem stalkModulePullbackFunctorIso_inv_app_unit
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y)) (U : Opens Y.carrier)
    (hx : f.hom.base x ∈ U) (s : M.val.obj (Opposite.op U)) :
    letI := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
    letI := Stacks.RingedSpace.structureStalkCommRing X x
    ((Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).inv.app M).hom
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap f x).hom).unit.app
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
              (f.hom.base x)).obj M)).hom
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U (f.hom.base x)
            hx).hom s)) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ((modulePullback f).obj M).val.presheaf
          ((AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).obj U) x hx).hom
        (((modulePullbackPushforwardAdjunction f).unit.app M).val.app (Opposite.op U) s) := by
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  exact (congrArg (fun φ => φ.val.app (Opposite.op U) s ⟨hx⟩)
    (unit_conjugateEquiv_symm (Stacks.RingedSpace.stalkPullbackAdjunction f x)
      (Stacks.RingedSpace.stalkBaseChangeAdjunction f x)
      (Stacks.RingedSpace.pushforwardSkyscraperIso f x).hom M)).symm

/-- **The stalk of the two-step pullback on the germ of a unit section.**  The identification
`stalkTwoStepPullbackIso` carries `1 ⊗ s_{f(x)}` to the germ at `x` of the image of `s` under
the unit of `twoStepPullbackAdjunction`. -/
theorem stalkTwoStepPullbackIso_inv_app_unit
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y)) (U : Opens Y.carrier)
    (hx : f.hom.base x ∈ U) (s : M.val.obj (Opposite.op U)) :
    letI := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
    letI := Stacks.RingedSpace.structureStalkCommRing X x
    ((stalkTwoStepPullbackIso f x).inv.app M).hom
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap f x).hom).unit.app
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
              (f.hom.base x)).obj M)).hom
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U (f.hom.base x)
            hx).hom s)) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ((twoStepPullback f).obj M).val.presheaf
          ((AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).obj U) x hx).hom
        (((twoStepPullbackAdjunction f).unit.app M).val.app (Opposite.op U) s) := by
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  have hu := congrArg (fun φ => φ.val.app (Opposite.op U) s)
    ((modulePullbackPushforwardAdjunction f).unit_leftAdjointUniq_hom_app
      (twoStepPullbackAdjunction f) M)
  refine (congrArg (fun t => ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).map ((modulePullbackIsoTwoStep f).hom.app M)).hom t)
    (stalkModulePullbackFunctorIso_inv_app_unit f x M U hx s)).trans ?_
  refine (AlgebraicGeometry.SheafOfModules.stalkMap_germ (structureSheafRing X) x _ _ hx _).trans ?_
  exact congrArg _ hu

/-- **Maps out of the stalk of a two-step pullback are determined on germs of unit sections.** -/
theorem stalkTwoStepPullback_hom_ext (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    {V : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x)}
    {a b : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      ((twoStepPullback f).obj M) ⟶ V}
    (hab : ∀ (U : Opens Y.carrier) (hx : f.hom.base x ∈ U) (s : M.val.obj (Opposite.op U)),
      a.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ((twoStepPullback f).obj M).val.presheaf
          ((AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).obj U) x hx).hom
        (((twoStepPullbackAdjunction f).unit.app M).val.app (Opposite.op U) s)) =
      b.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ((twoStepPullback f).obj M).val.presheaf
          ((AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).obj U) x hx).hom
        (((twoStepPullbackAdjunction f).unit.app M).val.app (Opposite.op U) s))) :
    a = b := by
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  rw [← cancel_epi ((stalkTwoStepPullbackIso f x).app M).inv]
  let N := (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
    (f.hom.base x)).obj M
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (Stacks.RingedSpace.stalkRingMap f x).hom
  refine (adj.homEquiv N V).injective ?_
  have ha := adj.homEquiv_unit (X := N) (Y := V)
    (f := (((stalkTwoStepPullbackIso f x).app M).inv ≫ a :
      (ModuleCat.extendScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap f x).hom).obj N ⟶ V))
  have hb := adj.homEquiv_unit (X := N) (Y := V)
    (f := (((stalkTwoStepPullbackIso f x).app M).inv ≫ b :
      (ModuleCat.extendScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap f x).hom).obj N ⟶ V))
  refine ha.trans (Eq.trans ?_ hb.symm)
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  exact (congrArg a.hom (stalkTwoStepPullbackIso_inv_app_unit f x M U hx s)).trans
    ((hab U hx s).trans (congrArg b.hom (stalkTwoStepPullbackIso_inv_app_unit f x M U hx s)).symm)

/-- **A map out of the stalk of a two-step pullback from a semilinear map out of the stalk.**
An `𝒪_{Y,f(x)}`-linear map `ν : M_{f(x)} ⟶ V` to an `𝒪_{X,x}`-module `V` extends to the
`𝒪_{X,x}`-linear map `(f^*M)_x ≅ 𝒪_{X,x} ⊗ M_{f(x)} ⟶ V`. -/
def stalkTwoStepPullbackDesc (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    {V : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x)}
    (ν : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        (f.hom.base x)).obj M ⟶
      (ModuleCat.restrictScalars.{u} (Stacks.RingedSpace.stalkRingMap f x).hom).obj V) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      ((twoStepPullback f).obj M) ⟶ V :=
  letI := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  letI := Stacks.RingedSpace.structureStalkCommRing X x
  ((stalkTwoStepPullbackIso f x).app M).hom ≫
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap f x).hom).homEquiv _ V).symm ν

/-- `stalkTwoStepPullbackDesc ν` carries the germ of a unit section to the value of `ν` on the
germ of the section. -/
theorem stalkTwoStepPullbackDesc_germ_unit
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    {V : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x)}
    (ν : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        (f.hom.base x)).obj M ⟶
      (ModuleCat.restrictScalars.{u} (Stacks.RingedSpace.stalkRingMap f x).hom).obj V)
    (U : Opens Y.carrier) (hx : f.hom.base x ∈ U) (s : M.val.obj (Opposite.op U)) :
    (stalkTwoStepPullbackDesc f x M ν).hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ((twoStepPullback f).obj M).val.presheaf
          ((AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).obj U) x hx).hom
        (((twoStepPullbackAdjunction f).unit.app M).val.app (Opposite.op U) s)) =
      ν.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U (f.hom.base x)
        hx).hom s) := by
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (Stacks.RingedSpace.stalkRingMap f x).hom
  refine (congrArg (stalkTwoStepPullbackDesc f x M ν).hom
    (stalkTwoStepPullbackIso_inv_app_unit f x M U hx s).symm).trans ?_
  have e1 : ((stalkTwoStepPullbackIso f x).app M).inv ≫ stalkTwoStepPullbackDesc f x M ν =
      (adj.homEquiv _ V).symm ν :=
    Iso.inv_hom_id_assoc _ _
  refine (congrArg (fun φ => φ.hom ((adj.unit.app _).hom ((TopCat.Presheaf.germ
    (C := AddCommGrpCat.{u}) M.val.presheaf U (f.hom.base x) hx).hom s))) e1).trans ?_
  have h := adj.homEquiv_unit (f := (adj.homEquiv _ V).symm ν)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun φ => φ.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf
    U (f.hom.base x) hx).hom s)) h).symm

end PullbackStalk

section Square

open Stacks.Sites.FreeAlgebra Stacks.SheafOfModules
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i]
  (i' : X' ⟶ P') (h' : P' ⟶ Y') [IsImmersion i'] (g' : X' ⟶ X) (p : P' ⟶ P)

/-- The kernel of the pullback along `g'` of the first arrow of `i`, in the two models of the
pullback: the two-step model `RingedSpaceModuleAdjunction.twoStepPullback`, which is the target
of `pulledComplexHomologyNegOneIso`, and `RingedSpaceModuleAdjunction.modulePullback`, read on
the categorical presentation of the conormal sheaf. -/
def kernelTwoStepPullbackIso :
    kernel ((twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential i h)) ≅
      kernel ((modulePullback g'.toLRSHom.toShHom).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential i h)) :=
  kernelIsoOfEq (map_eq_conj_of_iso (modulePullbackIsoTwoStep g'.toLRSHom.toShHom)
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i)
      (Stacks.ConormalSequenceRight.conormalDifferential i h)) ≪≫
    kernelConjIso _ _ _

/-- The degree `-2` term of the naive cotangent complex of the polynomial presentation of `𝒪_X`
on the sections of `i⁻¹𝒪_P` vanishes. -/
theorem isZero_presentationComplex_X_negTwo :
    IsZero ((presentationNaiveCotangentComplex.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i)))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i)))).X (-2)) :=
  presentationNaiveCotangentComplex_isZero_X.{u, u, u, u} _ _ _ _ _ _ (-2) (by decide)
    (by decide)

/-- The comparison of the polynomial presentation with `NL_{X/Y}` itself, for `f = i ≫ h`: the
comparison of [Stacks Project, Tag 08TL] followed by the identification of the iterated spelling
of `NL_{X/Y}` with `NL_{X/Y}`. -/
def presentationToNaiveCotangent :=
  presentationComparison i h ≫ (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv

/-- The map `presentationToNaiveCotangent` induces an isomorphism on `H^{-1}`. -/
instance isIso_homologyMap_presentationToNaiveCotangent :
    IsIso (HomologicalComplex.homologyMap (presentationToNaiveCotangent i h) (-1)) := by
  have := isIso_homologyMap_presentationComparison i h
  rw [presentationToNaiveCotangent, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **`H^{-1}(NL_{X/Y}) ≅ Ker(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`, followed by the inclusion of the kernel**:
it is the inverse of the map induced on `H^{-1}` by `presentationToNaiveCotangent`, followed by
the comparison with `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in degree `-1`. -/
theorem naiveCotangentHomologyNegOneIso_hom_ι (hg : Stacks.Smooth.FormallySmoothScheme h) :
    (naiveCotangentHomologyNegOneIso i h rfl hg).hom ≫
        kernel.ι (Stacks.ConormalSequenceRight.conormalDifferential i h) =
      inv (HomologicalComplex.homologyMap (presentationToNaiveCotangent i h) (-1)) ≫
        homologyNegOneι _ (isZero_presentationComplex_X_negTwo i h) ≫
        (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom).f (-1) ≫
        (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom :=
  zigzagHomologyNegOneIso_hom_ι (Stacks.NaiveCotangentTower.schemePresentationIso i h)
    (presentationComparison i h)
    (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)
    (isIso_homologyMap_presentationComparison i h)
    (isIso_homologyMap_negOne_of_quasiIso (quasiIso_conormalComparison i h hg))
    (isIso_homologyMap_presentationToNaiveCotangent i h)
    (isZero_presentationComplex_X_negTwo i h) (isZero_conormalDifferentialComplex_X_negTwo i h)
    (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h)
    (Stacks.ConormalSequenceRight.conormalDifferential i h)
    (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoZero i h)
    (Stacks.ConormalSequenceRight.conormalDifferentialComplex_d_negOne_zero i h) _

/-- The degree `-2` term of the pullback of the naive cotangent complex of the polynomial
presentation vanishes. -/
theorem isZero_pulled_presentationComplex_X_negTwo :
    IsZero (((pulledComplexFunctor g'.toLRSHom.toShHom).obj
      (presentationNaiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i)))
        (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom i))))).X (-2)) :=
  isZero_pulledComplexFunctor_obj_X _ _ _ (isZero_presentationComplex_X_negTwo i h)

/-- The pullback along `g'` of `presentationToNaiveCotangent` induces an isomorphism on
`H^{-1}`. -/
theorem isIso_homologyMap_pulled_presentationToNaiveCotangent :
    IsIso (HomologicalComplex.homologyMap
      ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
        (pulledComplexFunctor g'.toLRSHom.toShHom).map
          (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv) (-1)) := by
  rw [HomologicalComplex.homologyMap_comp]
  have := isIso_homologyMap_negOne_of_quasiIso (quasiIso_pulled_presentationComparison i h g')
  infer_instance

/-- **`H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*δ)`, followed by the inclusion of the kernel**, with
`(g')^*` the module pullback and `δ` read on the categorical presentation of the conormal
sheaf: it is the inverse of the map induced on `H^{-1}` by the pullback of
`presentationToNaiveCotangent`, followed by the pullback of the comparison with
`(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in degree `-1`. -/
theorem pulledComplexHomologyNegOneIso_trans_hom_ι (hg : Stacks.Smooth.FormallySmoothScheme h) :
    (pulledComplexHomologyNegOneIso i h g' (i ≫ h) rfl hg ≪≫
        kernelTwoStepPullbackIso i h g').hom ≫
        kernel.ι ((modulePullback g'.toLRSHom.toShHom).map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential i h)) =
      @inv _ _ _ _ (HomologicalComplex.homologyMap
          ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
            (pulledComplexFunctor g'.toLRSHom.toShHom).map
              (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv) (-1))
          (isIso_homologyMap_pulled_presentationToNaiveCotangent i h g') ≫
        homologyNegOneι _ (isZero_pulled_presentationComplex_X_negTwo i h g') ≫
        ((pulledComplexFunctor g'.toLRSHom.toShHom).map
          (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)).f (-1) ≫
        (twoStepPullback g'.toLRSHom.toShHom).map
          (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom ≫
        (modulePullbackIsoTwoStep g'.toLRSHom.toShHom).inv.app _ ≫
        (modulePullback g'.toLRSHom.toShHom).map
          (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom :=
  zigzagHomologyNegOneIso_trans_hom_ι
    ((pulledComplexFunctor g'.toLRSHom.toShHom).mapIso
      (Stacks.NaiveCotangentTower.schemePresentationIso i h))
    ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h))
    ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom))
    (isIso_homologyMap_negOne_of_quasiIso (quasiIso_pulled_presentationComparison i h g'))
    (isIso_homologyMap_negOne_of_quasiIso (quasiIso_pulled_conormalComparison i h g' hg))
    (isIso_homologyMap_pulled_presentationToNaiveCotangent i h g')
    (isZero_pulled_presentationComplex_X_negTwo i h g')
    (isZero_pulledComplexFunctor_obj_X _ _ _
      (Stacks.ConormalSequenceRight.conormalDifferentialComplex_isZero_X i h (-2)
        (by decide) (by decide)))
    ((twoStepPullback g'.toLRSHom.toShHom).mapIso
      (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h))
    ((twoStepPullback g'.toLRSHom.toShHom).map
      (Stacks.ConormalSequenceRight.conormalDifferential i h))
    ((twoStepPullback g'.toLRSHom.toShHom).mapIso
      (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoZero i h))
    (pulled_conormalDifferentialComplex_d i h g')
    (((modulePullbackIsoTwoStep g'.toLRSHom.toShHom).app _).symm ≪≫
      (modulePullback g'.toLRSHom.toShHom).mapIso
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i))
    ((modulePullback g'.toLRSHom.toShHom).map
      ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
        Stacks.ConormalSequenceRight.conormalDifferential i h))
    ((modulePullbackIsoTwoStep g'.toLRSHom.toShHom).app _).symm
    (map_eq_conj_of_iso (modulePullbackIsoTwoStep g'.toLRSHom.toShHom)
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i)
      (Stacks.ConormalSequenceRight.conormalDifferential i h)) _

/-- **Reduction of the comparison on `H^{-1}` to the polynomial presentations.**  For a
commutative square `i' ≫ p = g' ≫ i` of immersions with `h`, `h'` formally smooth, and any base
change map `bc` of naive cotangent complexes from `(g')^*NL_{X/Y}` to `NL_{X'/Y'}`, the map
induced on `H^{-1}` by `bc`, read through the identifications
`H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*δ)` and `H^{-1}(NL_{X'/Y'}) ≅ Ker δ'`, is the restriction of
the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of [Stacks Project, Tag 01R4] if and only if the following
holds on `H^{-1}` of the pulled-back polynomial presentation of `𝒪_X`: the map induced by the
comparison with `NL_{X'/Y'}`, followed by the inverse of the map induced by the polynomial
presentation of `𝒪_{X'}` and its comparison with `𝒞_{X'/P'}`, is the inclusion followed by the
pullback of the comparison with `𝒞_{X/P}` and the map of [Stacks Project, Tag 01R4]. -/
theorem homologyMap_negOne_comp_eq_iff (hg : Stacks.Smooth.FormallySmoothScheme h)
    (hg' : Stacks.Smooth.FormallySmoothScheme h')
    (bcm : Stacks.NaiveCotangentFlatBaseChange.pulledComplex (i ≫ h) g' ⟶
      Scheme.naiveCotangentComplex (i' ≫ h')) (hip : i' ≫ p = g' ≫ i) :
    ((pulledComplexHomologyNegOneIso i h g' (i ≫ h) rfl hg ≪≫
        kernelTwoStepPullbackIso i h g').inv ≫
      HomologicalComplex.homologyMap bcm (-1) ≫
      (naiveCotangentHomologyNegOneIso i' h' rfl hg').hom ≫
      kernel.ι (Stacks.ConormalSequenceRight.conormalDifferential i' h') =
    kernel.ι ((modulePullback g'.toLRSHom.toShHom).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential i h)) ≫
      Stacks.Immersion.immersionConormalSheafMap i' i g' p
        (Stacks.Immersion.toShHom_square hip) ≫
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').inv) ↔
    ((HomologicalComplex.homologyMap
        ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
          (pulledComplexFunctor g'.toLRSHom.toShHom).map
            (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv) (-1) ≫
        HomologicalComplex.homologyMap bcm (-1)) ≫
      inv (HomologicalComplex.homologyMap (presentationToNaiveCotangent i' h') (-1)) ≫
      homologyNegOneι _ (isZero_presentationComplex_X_negTwo i' h') ≫
      (Stacks.NaiveCotangentTower.schemeTowerComparison i' h' ≫ (towerIso i' h').hom).f (-1) ≫
      (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i' h').hom ≫
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').hom =
    homologyNegOneι _ (isZero_pulled_presentationComplex_X_negTwo i h g') ≫
      ((pulledComplexFunctor g'.toLRSHom.toShHom).map
        (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)).f (-1) ≫
      (twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom ≫
      (modulePullbackIsoTwoStep g'.toLRSHom.toShHom).inv.app _ ≫
      (modulePullback g'.toLRSHom.toShHom).map
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom ≫
      Stacks.Immersion.immersionConormalSheafMap i' i g' p
        (Stacks.Immersion.toShHom_square hip)) := by
  have := isIso_homologyMap_pulled_presentationToNaiveCotangent i h g'
  exact comp_eq_iff_of_comp_eq (ρ := HomologicalComplex.homologyMap
      ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
        (pulledComplexFunctor g'.toLRSHom.toShHom).map
          (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv) (-1))
    (q := HomologicalComplex.homologyMap (presentationToNaiveCotangent i' h') (-1))
    _ _ _ _ (pulledComplexHomologyNegOneIso_trans_hom_ι i h g' hg)
    _ _ _ _ _ (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').symm
    (naiveCotangentHomologyNegOneIso_hom_ι i' h' hg') _

end Square

end Stacks.NaiveCotangentPulledImmersion

end

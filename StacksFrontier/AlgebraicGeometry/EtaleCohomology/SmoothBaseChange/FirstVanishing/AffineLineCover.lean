module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GenericFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.LocalLifting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineLineGeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SlicingSmooth.AffineConnectedCover
public import StacksFrontier.AlgebraicGeometry.Etale.NormalSepClosedFunctionField
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono

/-!
# The local liftings over the affine line in the normalized diagram of Stacks 0F08

In the normalized diagram of Stacks 0F08 for the affine line,
```
𝔸¹_T  ←--  X'  ←-h-  Y
  |        |f'       |e
  T   ←s-  S'  ←-g-  Spec K
```
let `0 ⟶ ℤ/dℤ ⟶ F₂ ⟶ F₃ ⟶ 0` be short exact on `Y_étale`. This file shows that every section of
`F₃` over `V ×_{X'} Y`, for `V` étale over `X'`, lifts to `F₂` étale locally on `V`. This is the
final case `q = 1` of the second proof of Stacks 0EYU: around a point of `V`, Stacks 0EY4 and
09Z9 make `V ⟶ S'` a smooth morphism with geometrically connected fibres and a section over an
affine open of an open subscheme of `S'`, and the generic-fibre step
(`exists_finiteEtale_mapExactFunctor_eq_zero_of_genericFibre`, from Stacks 03SC (6) and 0EZJ)
kills the corresponding class on a finite étale surjective cover.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.topologicalKrullDim_pullback_le_one` — the fibres of an
  étale scheme over the affine line are curves.
* `Stacks.EtaleCohomology.SmoothBaseChange.exists_lift_of_genericFibreData` — a local lifting over
  an étale piece carrying the data of the generic-fibre step.
* `Stacks.EtaleCohomology.SmoothBaseChange.exists_lift_through_point` — a local lifting through
  every point.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EY4](https://stacks.math.columbia.edu/tag/0EY4)
* [Stacks Project, Tag 09Z9](https://stacks.math.columbia.edu/tag/09Z9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The fibres of an étale scheme over the affine line are curves.** Let `X' = 𝔸¹_{S'}`, let
`U ⟶ X'` be étale and let `f₀ : U ⟶ S₀` be a factorization of `U ⟶ X' ⟶ S'` through a
monomorphism `S₀ ⟶ S'`. Every fibre of `f₀` over a point `Spec κ ⟶ S₀`, a field `κ`, has
dimension at most one: it is étale over `𝔸¹_κ`. -/
theorem topologicalKrullDim_pullback_le_one {T S' X' S₀ U : Scheme.{u}} {s : S' ⟶ T}
    {p : X' ⟶ 𝔸(ULift.{u} (Fin 1); T)} {f' : X' ⟶ S'}
    (hp : IsPullback p f' (𝔸(ULift.{u} (Fin 1); T) ↘ T) s) (j : S₀ ⟶ S') [Mono j]
    (v : U ⟶ X') [Etale v] (f₀ : U ⟶ S₀) (hf : f₀ ≫ j = v ≫ f') (κ : Type u) [Field κ]
    (q : Spec (.of κ) ⟶ S₀) : topologicalKrullDim (pullback f₀ q : Scheme.{u}) ≤ 1 := by
  let m : pullback f₀ q ⟶ pullback f' (q ≫ j) := pullback.lift (pullback.fst _ _ ≫ v)
    (pullback.snd _ _) (by rw [Category.assoc, ← hf, pullback.condition_assoc])
  have hbig : IsPullback (m ≫ pullback.snd f' (q ≫ j)) (pullback.fst f₀ q) (q ≫ j) (v ≫ f') := by
    rw [pullback.lift_snd, ← hf]
    exact (IsPullback.of_hasPullback f₀ q).flip.comp_mono j
  have hleft : IsPullback m (pullback.fst f₀ q) (pullback.fst f' (q ≫ j)) v :=
    IsPullback.of_right hbig (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f' (q ≫ j)).flip
  have : Etale m := MorphismProperty.of_isPullback hleft.flip inferInstance
  refine (topologicalKrullDim_le_of_etale m).trans ?_
  have h₁ : IsPullback (pullback.fst f' (q ≫ j) ≫ p) (pullback.snd f' (q ≫ j))
      (𝔸(ULift.{u} (Fin 1); T) ↘ T) ((q ≫ j) ≫ s) :=
    (IsPullback.of_hasPullback f' (q ≫ j)).paste_horiz hp
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (h₁.isoIsPullback _ _
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) ((q ≫ j) ≫ s)))).isHomeomorph]
  exact topologicalKrullDim_affineLine_spec κ

/-- The residue field at the generic point of an integral scheme is its function field. -/
theorem isAlgClosed_residueField_genericPoint {S : Scheme.{u}} [IsIntegral S]
    [IsAlgClosed S.functionField] : IsAlgClosed (S.residueField (genericPoint S)) :=
  IsAlgClosed.of_ringEquiv S.functionField _ (RingEquiv.ofBijective (S.residue (genericPoint S)).hom
    ⟨(S.residue (genericPoint S)).hom.injective, S.residue_surjective _⟩)

/-- An open subscheme of an integral scheme with algebraically closed function field has an
algebraically closed residue field at its generic point. -/
theorem isAlgClosed_residueField_genericPoint_of_isOpenImmersion {S₀ S : Scheme.{u}}
    [IsIntegral S₀] [IsIntegral S] [IsAlgClosed S.functionField] (j : S₀ ⟶ S) [IsOpenImmersion j] :
    IsAlgClosed (S₀.residueField (genericPoint S₀)) := by
  have := isAlgClosed_residueField_genericPoint (S := S)
  have key : ∀ y (_ : j (genericPoint S₀) = y), IsAlgClosed (S.residueField y) →
      IsAlgClosed (S₀.residueField (genericPoint S₀)) := by
    rintro y rfl hy
    exact IsAlgClosed.of_ringEquiv _ _
      (asIso (j.residueFieldMap (genericPoint S₀))).commRingCatIsoToRingEquiv
  exact key _ (genericPoint_eq_of_isOpenImmersion j) inferInstance

/-- **A local lifting over an étale piece carrying the data of the generic-fibre step.** In the
normalized diagram of Stacks 0F08, let `0 ⟶ ℤ/dℤ ⟶ F₂ ⟶ F₃ ⟶ 0` be short exact on `Y_étale`,
`c` a section of `F₃` over `V ×_{X'} Y` and `a : U ⟶ V` étale such that `U ⟶ S'` factors as a
smooth morphism `f₀ : U ⟶ S₀` with geometrically connected fibres and a section, followed by an
open immersion `S₀ ⟶ S'` from a quasi-compact integral normal scheme. Then there is an étale
`Z ⟶ V` whose image contains that of `U`, over which `c` lifts to `F₂`. -/
theorem exists_lift_of_genericFibreData (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EZJ : GaloisCoversExtendFromGenericFiber.{u}) {T S' X' Y : Scheme.{u}} {s : S' ⟶ T}
    {p : X' ⟶ 𝔸(ULift.{u} (Fin 1); T)} {f' : X' ⟶ S'}
    (hp : IsPullback p f' (𝔸(ULift.{u} (Fin 1); T) ↘ T) s)
    {K : Type u} [Field K] [IsAlgClosed K] {g : Spec (.of K) ⟶ S'} {h : Y ⟶ X'}
    {e : Y ⟶ Spec (.of K)} (sq : IsPullback h e f' g)
    {Sh : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : Sh.ShortExact)
    (d : ℕ) (hd : 0 < d) (eG : Sh.X₁ ≅ FirstFailureDiagram.constantZMod Y d)
    {V : X'.Etale} (c : Sh.X₃.obj.obj (op ((smallEtaleBaseChange h).obj V)))
    (U : X'.Etale) (a : U ⟶ V)
    (S₀ : Scheme.{u}) [CompactSpace S₀] [QuasiSeparatedSpace S₀] [IsIntegral S₀] [IsNormal S₀]
    [IsAlgClosed (S₀.residueField (genericPoint S₀))]
    (j : S₀ ⟶ S') [IsOpenImmersion j] (f₀ : U.left ⟶ S₀) [QuasiCompact f₀] [QuasiSeparated f₀]
    [Smooth f₀] [GeometricallyConnected f₀] [IsSeparated f₀]
    (σ : S₀ ⟶ U.left) (hσ : σ ≫ f₀ = 𝟙 S₀) (hf : f₀ ≫ j = U.hom ≫ f')
    (g₀ : Spec (.of K) ⟶ S₀) [IsDominant g₀] (hg : g₀ ≫ j = g)
    (hdS : ∀ x : S₀, IsUnit (d : S₀.residueField x)) :
    ∃ (Z : X'.Etale) (b : Z ⟶ V), Set.range a.left.base ⊆ Set.range b.left.base ∧
      ∃ i : Sh.X₂.obj.obj (op ((smallEtaleBaseChange h).obj Z)),
        Sh.g.hom.app _ i = Sh.X₃.obj.map ((smallEtaleBaseChange h).map b).op c := by
  let bc := smallEtaleBaseChange h
  let W := bc.obj U
  let c₁ := Sh.X₃.obj.map (bc.map a).op c
  have sqW : IsPullback (pullback.fst U.hom h) (pullback.snd U.hom h ≫ e) f₀ g₀ :=
    IsPullback.of_comp_mono' j (by
      rw [hf, hg]
      exact (IsPullback.of_hasPullback U.hom h).paste_vert sq)
  let eA : (etaleRestriction.{u, 0} W.hom).obj Sh.X₁ ≅ FirstFailureDiagram.constantZMod W.left d :=
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} W.hom).symm.app _) ≪≫
      (etaleAbelianInverseImage.{u, 0} W.hom).mapIso eG ≪≫
        (etaleAbelianInverseImageConstantIso.{u, 0} W.hom).app _
  have hdim : topologicalKrullDim (f₀.fiber (genericPoint S₀)) ≤ 1 :=
    topologicalKrullDim_pullback_le_one hp j U.hom f₀ hf _ (S₀.fromSpecResidueField _)
  obtain ⟨Y', π, hfin, het, hsurj, hdie⟩ :=
    exists_finiteEtale_mapExactFunctor_eq_zero_of_genericFibre h03SC6 h0EZJ f₀ σ hσ hdim K g₀
      (pullback.fst U.hom h) (pullback.snd U.hom h ≫ e) sqW d hd hdS eA
      (restrictedBoundaryClass hS c₁)
  let Z : X'.Etale := Scheme.Etale.mk (π ≫ U.hom)
  let bZ : Z ⟶ U := MorphismProperty.Over.homMk π rfl
  refine ⟨Z, bZ ≫ a, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj.surj x
    exact ⟨y, rfl⟩
  · obtain ⟨i, hi⟩ := exists_lift_of_restrictedBoundaryClass hS c₁ (bc.map bZ)
      (hdie ((bc.map bZ).left) (pullback.fst Z.hom h)
        (smallEtaleBaseChange_map_left_fst h bZ))
    refine ⟨i, hi.trans ?_⟩
    show (Sh.X₃.obj.map (bc.map a).op ≫ Sh.X₃.obj.map (bc.map bZ).op) c = _
    rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp]

/-- An étale separated scheme `B` over an integral normal scheme `S` with separably closed
function field is locally an open subscheme of `S`: every point of `B` has an affine open
neighbourhood on which `B ⟶ S` is an open immersion. -/
private theorem exists_isAffineOpen_isOpenImmersion_of_etale {S B : Scheme.{u}} [IsIntegral S]
    [IsNormal S] [IsSepClosed S.functionField] (hB : B ⟶ S) [Etale hB] [IsSeparated hB] (b : B) :
    ∃ W : B.Opens, IsAffineOpen W ∧ b ∈ W ∧ IsOpenImmersion (W.ι ≫ hB) := by
  obtain ⟨I, Vs, js, hjs, eB, heB⟩ := exists_coproduct_open_immersions S B hB
  obtain ⟨⟨k, w⟩, hkw⟩ := (sigmaMk Vs).surjective (eB.hom b)
  rw [sigmaMk_mk] at hkw
  let ιk := Sigma.ι Vs k ≫ eB.inv
  have hιk : ιk ≫ hB = js k := by
    simp only [ιk, Category.assoc, ← heB, Iso.inv_hom_id_assoc, Sigma.ι_desc]
  have hbO : b ∈ ιk.opensRange := ⟨w, by
    show (Sigma.ι Vs k ≫ eB.inv) w = b
    rw [Scheme.Hom.comp_apply, hkw, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl⟩
  obtain ⟨W, hWaff, hbW, hWle⟩ := exists_isAffineOpen_mem_and_subset hbO
  let l : (W : Scheme.{u}) ⟶ Vs k := IsOpenImmersion.lift ιk W.ι (by
    rw [Scheme.Opens.range_ι]
    exact hWle)
  have hl : l ≫ ιk = W.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W, hWaff, hbW, ?_⟩
  rw [← hl, Category.assoc, hιk]
  infer_instance

/-- A dominant morphism from the spectrum of a field to an integral scheme factors, as a dominant
morphism, through every open immersion from an integral scheme. -/
private theorem exists_isDominant_lift_of_isOpenImmersion {S W : Scheme.{u}} [IsIntegral S]
    [IsIntegral W] {K : Type u} [Field K] (g : Spec (.of K) ⟶ S) [IsDominant g] (j : W ⟶ S)
    [IsOpenImmersion j] : ∃ g₀ : Spec (.of K) ⟶ W, IsDominant g₀ ∧ g₀ ≫ j = g := by
  obtain ⟨φ, hφ⟩ := exists_spec_map_comp_fromSpecResidueField_eq g
  have hgen : ∀ z, g z = genericPoint S := fun z => by
    rw [← hφ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hrange : Set.range g.base ⊆ Set.range j.base := by
    rintro _ ⟨z, rfl⟩
    rw [hgen, ← genericPoint_eq_of_isOpenImmersion j]
    exact ⟨_, rfl⟩
  let g₀ : Spec (.of K) ⟶ W := IsOpenImmersion.lift j g hrange
  have hg₀ : g₀ ≫ j = g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨g₀, ⟨?_⟩, hg₀⟩
  obtain ⟨z⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hpt : g₀ z = genericPoint W := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hg₀, hgen, genericPoint_eq_of_isOpenImmersion j]
  rw [DenseRange, dense_iff_closure_eq]
  have h₁ : closure ({genericPoint W} : Set W) = Set.univ := genericPoint_spec W
  exact Set.eq_univ_of_univ_subset (h₁ ▸ closure_mono (Set.singleton_subset_iff.2 ⟨z, hpt⟩))

/-- A section of `f : X ⟶ Y` restricts to a section of `f ∣_ W` over every open `W` of `Y`. -/
private theorem exists_section_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) (W : Y.Opens) :
    ∃ σ₀ : (W : Scheme.{u}) ⟶ (f ⁻¹ᵁ W : Scheme.{u}), σ₀ ≫ (f ∣_ W) = 𝟙 _ := by
  have hσrange : Set.range (W.ι ≫ σ).base ⊆ Set.range (f ⁻¹ᵁ W).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f (σ (W.ι x)) ∈ W
    rw [← Scheme.Hom.comp_apply, hσ]
    exact x.2
  refine ⟨IsOpenImmersion.lift _ _ hσrange, ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι,
    IsOpenImmersion.lift_fac_assoc, Category.assoc, hσ, Category.comp_id, Category.id_comp]

/-- **A local lifting through every point**, in the normalized diagram of Stacks 0F08: for every
section `c` of `F₃` over `V ×_{X'} Y` and every point `v` of `V`, there is an étale `Z ⟶ V` through
whose image `v` passes, over which `c` lifts to `F₂`. Locally around `v` the morphism
`V ⟶ S'` is a smooth morphism with a section and geometrically connected fibres followed by an
étale `B ⟶ S'` (Stacks 0EY4), and `B` is locally an open subscheme of `S'` (Stacks 09Z9), so the
generic-fibre step applies over an affine open of `B`. -/
theorem exists_lift_through_point (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EZJ : GaloisCoversExtendFromGenericFiber.{u}) {T S' X' Y : Scheme.{u}} {s : S' ⟶ T}
    {p : X' ⟶ 𝔸(ULift.{u} (Fin 1); T)} {f' : X' ⟶ S'}
    (hp : IsPullback p f' (𝔸(ULift.{u} (Fin 1); T) ↘ T) s) [IsAffine S'] [IsIntegral S']
    (hnorm : IsNormalDomain Γ(S', ⊤)) [IsAlgClosed S'.functionField]
    {K : Type u} [Field K] [IsAlgClosed K] {g : Spec (.of K) ⟶ S'} [IsDominant g] {h : Y ⟶ X'}
    {e : Y ⟶ Spec (.of K)} (sq : IsPullback h e f' g)
    {Sh : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : Sh.ShortExact)
    (d : ℕ) (hd : 0 < d) (hdunit : IsUnit ((d : ℤ) : Γ(S', ⊤)))
    (eG : Sh.X₁ ≅ FirstFailureDiagram.constantZMod Y d)
    {V : X'.Etale} (c : Sh.X₃.obj.obj (op ((smallEtaleBaseChange h).obj V))) (v : V.left) :
    ∃ (Z : X'.Etale) (b : Z ⟶ V), v ∈ Set.range b.left.base ∧
      ∃ i : Sh.X₂.obj.obj (op ((smallEtaleBaseChange h).obj Z)),
        Sh.g.hom.app _ i = Sh.X₃.obj.map ((smallEtaleBaseChange h).map b).op c := by
  have : IsNormal S' := by
    have : IsNormal (Spec Γ(S', ⊤)) := isNormal_spec_of_isIntegrallyClosed Γ(S', ⊤)
    exact isNormal_of_etale S'.isoSpec.hom
  have : Smooth (𝔸(ULift.{u} (Fin 1); T) ↘ T) := affineSpace_smooth_over
  have : Smooth f' := MorphismProperty.of_isPullback hp inferInstance
  obtain ⟨𝒰, H⟩ := exists_etaleCover_factors_affine_smooth_section (V.hom ≫ f')
  have h₀ := 𝒰.mem₀
  change 𝒰.presieve₀ ∈ Scheme.precoverage @Etale V.left at h₀
  obtain ⟨i₀, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 h₀).1 v
  have : Etale (𝒰.f i₀) := ((Scheme.presieve₀_mem_precoverage_iff _).1 h₀).2 i₀
  change 𝒰.f i₀ y = v at hy
  obtain ⟨B, hB, gi, σi, hBet, hUaff, hBaff, hsm, hσ, hgc, hfac⟩ := H i₀
  obtain ⟨W₀, hW₀aff, hbW₀, hj⟩ := exists_isAffineOpen_isOpenImmersion_of_etale hB (gi y)
  have : IsAffine W₀ := hW₀aff
  let j : (W₀ : Scheme.{u}) ⟶ S' := W₀.ι ≫ hB
  have : IsOpenImmersion j := hj
  have : Nonempty W₀ := ⟨⟨gi y, hbW₀⟩⟩
  have : IsIntegral W₀ := isIntegral_of_isOpenImmersion j
  have : IsNormal W₀ := isNormal_of_etale j
  have : IsAlgClosed ((W₀ : Scheme.{u}).residueField (genericPoint W₀)) :=
    isAlgClosed_residueField_genericPoint_of_isOpenImmersion j
  let U' := gi ⁻¹ᵁ W₀
  let U : X'.Etale := Scheme.Etale.mk (U'.ι ≫ 𝒰.f i₀ ≫ V.hom)
  let a : U ⟶ V := MorphismProperty.Over.homMk (U'.ι ≫ 𝒰.f i₀) (Category.assoc _ _ _)
  let f₀ : U.left ⟶ W₀ := gi ∣_ W₀
  have hpb := (isPullback_morphismRestrict gi W₀).flip
  have : QuasiCompact f₀ := MorphismProperty.of_isPullback hpb inferInstance
  have : QuasiSeparated f₀ := MorphismProperty.of_isPullback hpb inferInstance
  have : Smooth f₀ := MorphismProperty.of_isPullback hpb inferInstance
  have : GeometricallyConnected f₀ := MorphismProperty.of_isPullback hpb inferInstance
  have : IsSeparated f₀ := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨σ₀, hσ₀⟩ := exists_section_morphismRestrict gi σi hσ W₀
  have hf : f₀ ≫ j = U.hom ≫ f' := by
    show (gi ∣_ W₀) ≫ W₀.ι ≫ hB = (U'.ι ≫ 𝒰.f i₀ ≫ V.hom) ≫ f'
    rw [morphismRestrict_ι_assoc, hfac]
    simp only [Category.assoc]
    rfl
  obtain ⟨g₀, _, hg₀⟩ := exists_isDominant_lift_of_isOpenImmersion g j
  have hdS (x : (W₀ : Scheme.{u})) : IsUnit (d : (W₀ : Scheme.{u}).residueField x) := by
    simpa using hdunit.map
      (j.appTop ≫ (W₀ : Scheme.{u}).presheaf.germ ⊤ x trivial ≫ (W₀ : Scheme.{u}).residue x).hom
  obtain ⟨Z, b, hab, hlift⟩ := exists_lift_of_genericFibreData h03SC6 h0EZJ hp sq hS d hd eG c U a
    W₀ j f₀ σ₀ hσ₀ hf g₀ hg₀ hdS
  exact ⟨Z, b, hab ⟨⟨y, hbW₀⟩, hy⟩, hlift⟩

end Stacks.EtaleCohomology.SmoothBaseChange

end

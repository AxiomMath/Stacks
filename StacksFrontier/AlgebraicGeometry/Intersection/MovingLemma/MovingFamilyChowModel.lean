module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectiveLineBridge
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints
public import
  StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ConjugateComponentDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints

/-!
# The moving family over the projective line of the Chow chapter

Tag 0B1T is formalized with its family inside `𝐏(W) ×_k 𝐏(V)` for a plane `W`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed`), while the
fibre cycles, the rational equivalences and the degeneration lemma Tag 0B1M of the intersection
chapter live on `𝐏(V) ×_k ℙ¹ = Stacks.Chow.projectiveLineProduct`, with the fibres over `0` and `∞`
cut out by `Stacks.Chow.zeroSection` and `Stacks.Chow.infinitySection`. This file carries the
family across the identification of the two ambient spaces built from
`AlgebraicGeometry.ProjectiveLineBridge.relativeProjectiveLineIsoProjectiveSpaceOfModule`.

## Main definitions

* `AlgebraicGeometry.ProjectiveLineBridge.lineProductIsoProjectiveLineProduct`: the isomorphism
  `𝐏(k²) ×_k 𝐏(V) ≅ 𝐏(V) ×_k ℙ¹` over `𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveLineBridge.lineProductSection_zeroPoint_comp_hom` and
  `AlgebraicGeometry.ProjectiveLineBridge.lineProductSection_infinityPoint_comp_hom`: the fibres
  over `0` and `∞` correspond to the zero and infinity sections.
* `AlgebraicGeometry.ProjectiveLineBridge.exists_movingFamily_projectiveLineProduct`: the four
  clauses of Tag 0B1T for a family in `Stacks.Chow.projectiveLineProduct`, with `C'_0` the
  scheme-theoretic zero fibre `Stacks.Chow.zeroFiber` and `C'_∞` the preimage along the infinity
  section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveLineBridge

open ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]

/-- The standard plane `k²`. -/
abbrev Plane : Type u := Fin 2 → k

/-- Its standard basis. -/
abbrev planeBasis : Module.Basis (Fin 2) k (Plane k) := Pi.basisFun k (Fin 2)

/-- The inverse of the identification `ℙ¹ ≅ 𝐏(k²)` commutes with the structure morphisms to
`Spec k`. -/
theorem inv_comp_relativeProjectiveLine_over :
    (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv ≫
        (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) =
      projectiveSpaceOfModuleToSpec k (Plane k) := by
  rw [Iso.inv_comp_eq, relativeProjectiveLineIsoProjectiveSpaceOfModule_hom_comp_toSpec]

/-- **`𝐏(k²) ×_k 𝐏(V) ≅ 𝐏(V) ×_k ℙ¹`**, the identification of the two ambient spaces of a family
of subvarieties of `𝐏(V)` over a projective line. -/
def lineProductIsoProjectiveLineProduct :
    lineProduct k V (Plane k) ≅
      Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V) :=
  pullbackSymmetry _ _ ≪≫
    asIso (pullback.map (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k (Plane k)) (projectiveSpaceOfModuleToSpec k V)
      (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv (𝟙 _)
      (by simp) (by rw [inv_comp_relativeProjectiveLine_over, Category.comp_id]))

/-- The isomorphism `lineProductIsoProjectiveLineProduct` commutes with the projections to
`𝐏(V)`. -/
@[reassoc (attr := simp)]
theorem lineProductIsoProjectiveLineProduct_hom_fst :
    (lineProductIsoProjectiveLineProduct k V).hom ≫ pullback.fst _ _ = lineProductPoint k V _ := by
  simp [lineProductIsoProjectiveLineProduct]

/-- Composed with the projection to `ℙ¹`, the isomorphism `lineProductIsoProjectiveLineProduct`
is the projection to `𝐏(k²)` followed by the identification `𝐏(k²) ≅ ℙ¹`. -/
@[reassoc (attr := simp)]
theorem lineProductIsoProjectiveLineProduct_hom_snd :
    (lineProductIsoProjectiveLineProduct k V).hom ≫ pullback.snd _ _ =
      lineProductLine k V _ ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv := by
  simp [lineProductIsoProjectiveLineProduct]

/-- Pointwise form of `lineProductIsoProjectiveLineProduct_hom_fst`. -/
private theorem lineProductIsoProjectiveLineProduct_hom_fst_apply (x : lineProduct k V (Plane k)) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
      (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))
        ((lineProductIsoProjectiveLineProduct k V).hom x) = (lineProductPoint k V (Plane k)) x := by
  rw [← Scheme.Hom.comp_apply, lineProductIsoProjectiveLineProduct_hom_fst]

/-- Pointwise form of `lineProductIsoProjectiveLineProduct_hom_snd`. -/
private theorem lineProductIsoProjectiveLineProduct_hom_snd_apply (x : lineProduct k V (Plane k)) :
    (pullback.snd (projectiveSpaceOfModuleToSpec k V)
      (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))
        ((lineProductIsoProjectiveLineProduct k V).hom x) =
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv
        ((lineProductLine k V (Plane k)) x) := by
  rw [← Scheme.Hom.comp_apply, lineProductIsoProjectiveLineProduct_hom_snd, Scheme.Hom.comp_apply]

/-- A `k`-point of `𝐏(k²)` whose image in the relative projective line is the closed point of a
section `s` is identified with `s` by the inverse of `ℙ¹ ≅ 𝐏(k²)`. -/
private theorem pointOfClosedPoint_comp_inv_eq (p : projectiveSpaceOfModule k (Plane k))
    (hp : IsClosed {p})
    (s : Spec (.of k) ⟶ Stacks.Chow.relativeProjectiveLine (Spec (.of k))) [IsClosedImmersion s]
    (hs : s ≫ (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _)
    (hp' : (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv p =
      s (IsLocalRing.closedPoint k)) :
    pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (Plane k)) p hp ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv = s := by
  have : IsProper (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    inferInstance
  refine ext_of_apply_closedPoint_eq_of_comp_eq
    (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
    (x := s (IsLocalRing.closedPoint k)) (isClosed_singleton_of_isClosedImmersion k _) ?_ rfl ?_
  · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ (pointOfClosedPoint_apply ..)).trans hp')
  · rw [Category.assoc, inv_comp_relativeProjectiveLine_over, pointOfClosedPoint_comp, hs]

/-- The `k`-point of `𝐏(k²)` at `0`, read in the relative projective line, is the zero
section. -/
theorem pointOfClosedPoint_zeroPoint_comp_inv :
    pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (Plane k)) (zeroPoint k _ (planeBasis k))
        (isClosed_zeroPoint k _ (planeBasis k)) ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv =
      Stacks.Chow.lineZeroSection (Spec (.of k)) := by
  refine pointOfClosedPoint_comp_inv_eq k _ _ _ (Stacks.Chow.lineZeroSection_comp _) ?_
  rw [zeroPoint, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- The `k`-point of `𝐏(k²)` at `∞`, read in the relative projective line, is the infinity
section. -/
theorem pointOfClosedPoint_infinityPoint_comp_inv :
    pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (Plane k))
        (infinityPoint k _ (planeBasis k)) (isClosed_infinityPoint k _ (planeBasis k)) ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).inv =
      Stacks.Chow.lineInfinitySection (Spec (.of k)) := by
  refine pointOfClosedPoint_comp_inv_eq k _ _ _ (Stacks.Chow.lineInfinitySection_comp _) ?_
  rw [infinityPoint, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

variable [FiniteDimensional k V] [Nontrivial V]

/-- **The fibre over `0` is the zero section.** -/
theorem lineProductSection_zeroPoint_comp_hom :
    lineProductSection k V (Plane k) (zeroPoint k _ (planeBasis k))
        (isClosed_zeroPoint k _ (planeBasis k)) ≫ (lineProductIsoProjectiveLineProduct k V).hom =
      Stacks.Chow.zeroSection (projectiveSpaceOfModuleToSpec k V) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, lineProductIsoProjectiveLineProduct_hom_fst,
      lineProductSection_comp_lineProductPoint, Stacks.Chow.zeroSection_comp_fst]
  · rw [Category.assoc, lineProductIsoProjectiveLineProduct_hom_snd,
      lineProductSection_comp_lineProductLine_assoc, pointOfClosedPoint_zeroPoint_comp_inv,
      Stacks.Chow.zeroSection_comp_snd]

/-- **The fibre over `∞` is the infinity section.** -/
theorem lineProductSection_infinityPoint_comp_hom :
    lineProductSection k V (Plane k) (infinityPoint k _ (planeBasis k))
        (isClosed_infinityPoint k _ (planeBasis k)) ≫
        (lineProductIsoProjectiveLineProduct k V).hom =
      Stacks.Chow.infinitySection (projectiveSpaceOfModuleToSpec k V) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, lineProductIsoProjectiveLineProduct_hom_fst,
      lineProductSection_comp_lineProductPoint, Stacks.Chow.infinitySection_comp_fst]
  · rw [Category.assoc, lineProductIsoProjectiveLineProduct_hom_snd,
      lineProductSection_comp_lineProductLine_assoc, pointOfClosedPoint_infinityPoint_comp_inv,
      Stacks.Chow.infinitySection_comp_snd]

/-- The dimension of a subset is unchanged by an isomorphism of schemes. -/
theorem topologicalKrullDim_image_hom {A B : Scheme.{u}} (e : A ≅ B) (S : Set A) :
    topologicalKrullDim ↥(e.hom.base '' S) = topologicalKrullDim ↥S :=
  topologicalKrullDim_image_homeomorph (Scheme.homeoOfIso e) S

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The isomorphism `lineProductIsoProjectiveLineProduct` carries the constant family
`lineProductConstant` of `X` onto the preimage of `X` in `𝐏(V) ×_k ℙ¹`. -/
private theorem preimage_fst_eq_image_lineProductConstant (X : Set (projectiveSpaceOfModule k V)) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X =
      (lineProductIsoProjectiveLineProduct k V).hom.base ''
        lineProductConstant k V (Plane k) X := by
  set hh := Scheme.homeoOfIso (lineProductIsoProjectiveLineProduct k V)
  have hhΦ : ∀ x, hh x = (lineProductIsoProjectiveLineProduct k V).hom.base x := fun _ => rfl
  ext y
  constructor
  · intro hy
    refine ⟨hh.symm y, ?_, hh.apply_symm_apply y⟩
    show (lineProductPoint k V (Plane k)) (hh.symm y) ∈ X
    rwa [← lineProductIsoProjectiveLineProduct_hom_fst_apply, ← hhΦ, hh.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    show (pullback.fst (projectiveSpaceOfModuleToSpec k V)
      (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))
        ((lineProductIsoProjectiveLineProduct k V).hom x) ∈ X
    rwa [lineProductIsoProjectiveLineProduct_hom_fst_apply]

/-- The preimage along `Stacks.Chow.infinitySection` of the image of `S` under
`lineProductIsoProjectiveLineProduct` is the fibre of `S` over `∞`. -/
private theorem infinitySection_preimage_image_hom (S : Set (lineProduct k V (Plane k))) :
    (Stacks.Chow.infinitySection (projectiveSpaceOfModuleToSpec k V)).base ⁻¹'
        ((lineProductIsoProjectiveLineProduct k V).hom.base '' S) =
      lineProductFibre k V (Plane k) (infinityPoint k _ (planeBasis k))
        (isClosed_infinityPoint k _ (planeBasis k)) S := by
  set hh := Scheme.homeoOfIso (lineProductIsoProjectiveLineProduct k V)
  have hhΦ : ∀ x, hh x = (lineProductIsoProjectiveLineProduct k V).hom.base x := fun _ => rfl
  have himg : hh '' S = (lineProductIsoProjectiveLineProduct k V).hom.base '' S := rfl
  ext y
  rw [Set.mem_preimage, ← lineProductSection_infinityPoint_comp_hom, Scheme.Hom.comp_apply,
    ← himg, ← hhΦ, hh.injective.mem_set_image]
  rfl

/-- **Tag 0B1T in the model `𝐏(V) ×_k ℙ¹` of the Chow chapter.** Let `C` be a closed subvariety
of `𝐏(V)`, `X` a subvariety of `𝐏(V)` (irreducible and locally closed) and `T i ⊆ X` finitely many
closed subvarieties of `X`, and suppose `C` and `X` intersect properly. Then there is a closed
subvariety `C'` of `Stacks.Chow.projectiveLineProduct (𝐏(V) ⟶ Spec k)` with

1. `C' → ℙ¹` dominant;
2. `C'_0 = C` scheme theoretically: the zero fibre `Stacks.Chow.zeroFiber` of the reduced closed
   subscheme on `C'` is the reduced closed subscheme on `C`;
3. `C'` and `X × ℙ¹` intersect properly;
4. the fibre `C'_∞`, the preimage of `C'` along `Stacks.Chow.infinitySection`, intersects each
   `T i` properly.

This is `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` over
the line `𝐏(k²)` with its points `0` and `∞`, carried along
`AlgebraicGeometry.ProjectiveLineBridge.lineProductIsoProjectiveLineProduct`. -/
public theorem exists_movingFamily_projectiveLineProduct
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) + topologicalKrullDim ↥X)
    {ι : Type*} [Finite ι] (T : ι → Set (projectiveSpaceOfModule k V))
    (hTX : ∀ i, T i ⊆ X) (hTc : ∀ i, IsClosed {x : X | x.1 ∈ T i})
    (hTirr : ∀ i, IsIrreducible (T i)) :
    ∃ Cfam : IrreducibleCloseds
        (Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)),
      closure ((pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ''
          (Cfam : Set (Stacks.Chow.projectiveLineProduct
            (projectiveSpaceOfModuleToSpec k V)))) = Set.univ ∧
      Stacks.Chow.zeroFiber (projectiveSpaceOfModuleToSpec k V)
          (Scheme.IdealSheafData.vanishingIdeal (⟨(Cfam : Set (Stacks.Chow.projectiveLineProduct
              (projectiveSpaceOfModuleToSpec k V))), Cfam.isClosed'⟩ :
            Closeds (Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))) =
        Scheme.IdealSheafData.vanishingIdeal
          (⟨C, C.isClosed'⟩ : Closeds (projectiveSpaceOfModule k V)) ∧
      topologicalKrullDim ↥((Cfam : Set (Stacks.Chow.projectiveLineProduct
            (projectiveSpaceOfModuleToSpec k V))) ∩
            (pullback.fst (projectiveSpaceOfModuleToSpec k V)
              (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X) +
          topologicalKrullDim
            (Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)) ≤
        topologicalKrullDim ↥(Cfam : Set (Stacks.Chow.projectiveLineProduct
            (projectiveSpaceOfModuleToSpec k V))) +
          topologicalKrullDim ↥((pullback.fst (projectiveSpaceOfModuleToSpec k V)
              (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X) ∧
      ∀ i, topologicalKrullDim
            ↥((Stacks.Chow.infinitySection (projectiveSpaceOfModuleToSpec k V)).base ⁻¹'
              (Cfam : Set (Stacks.Chow.projectiveLineProduct
                (projectiveSpaceOfModuleToSpec k V))) ∩ T i) +
          topologicalKrullDim (projectiveSpaceOfModule k V) ≤
        topologicalKrullDim
            ↥((Stacks.Chow.infinitySection (projectiveSpaceOfModuleToSpec k V)).base ⁻¹'
              (Cfam : Set (Stacks.Chow.projectiveLineProduct
                (projectiveSpaceOfModuleToSpec k V)))) +
          topologicalKrullDim ↥(T i) := by
  obtain ⟨Cf, h1, h2, h3, h4⟩ := exists_movingFamily_of_subvariety_fixed k V C X hX hXirr hCX T
    hTX hTc hTirr (Plane k) (by simp) (zeroPoint k _ (planeBasis k))
    (infinityPoint k _ (planeBasis k)) (isClosed_zeroPoint k _ (planeBasis k))
    (isClosed_infinityPoint k _ (planeBasis k)) (zeroPoint_ne_infinityPoint k _ (planeBasis k))
  have hsnd := lineProductIsoProjectiveLineProduct_hom_snd_apply k V
  have hpre := preimage_fst_eq_image_lineProductConstant k V X
  have hfib := infinitySection_preimage_image_hom k V (Cf : Set (lineProduct k V (Plane k)))
  set Φ := lineProductIsoProjectiveLineProduct k V
  set hh := Scheme.homeoOfIso Φ
  have hhΦ : ∀ x, hh x = Φ.hom.base x := fun _ => rfl
  have himg : ∀ S : Set (lineProduct k V (Plane k)), hh '' S = Φ.hom.base '' S := fun S => rfl
  let Cfam : IrreducibleCloseds
      (Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)) :=
    ⟨Φ.hom.base '' (Cf : Set (lineProduct k V (Plane k))),
      Cf.isIrreducible.image _ Φ.hom.continuous.continuousOn,
      (himg _) ▸ hh.isClosedMap _ Cf.isClosed'⟩
  have hCfam : (Cfam : Set (Stacks.Chow.projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))
      = Φ.hom.base '' (Cf : Set (lineProduct k V (Plane k))) := rfl
  refine ⟨Cfam, ?_, ?_, ?_, fun i => ?_⟩
  · rw [hCfam, Set.image_image]
    simp_rw [hsnd]
    rw [← Set.image_image (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k)
      (planeBasis k)).inv.base]
    have := (Scheme.homeoOfIso (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k)
      (planeBasis k)).symm).image_closure
      ((lineProductLine k V (Plane k)).base '' (Cf : Set (lineProduct k V (Plane k))))
    rw [Scheme.coe_homeoOfIso, Iso.symm_hom] at this
    rw [← this, h1, Set.image_univ]
    exact (Scheme.homeoOfIso
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k (Plane k) (planeBasis k)).symm).range_coe
  · rw [Stacks.Chow.zeroFiber, ← lineProductSection_zeroPoint_comp_hom,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_vanishingIdeal]
    refine Eq.trans ?_ h2
    congr 2
    apply Closeds.ext
    ext x
    show Φ.hom.base x ∈ Φ.hom.base '' (Cf : Set (lineProduct k V (Plane k))) ↔
      x ∈ (Cf : Set (lineProduct k V (Plane k)))
    rw [← himg, ← hhΦ, hh.injective.mem_set_image]
  · have hinter : (Φ.hom.base '' (Cf : Set (lineProduct k V (Plane k)))) ∩
        (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X =
        Φ.hom.base '' ((Cf : Set (lineProduct k V (Plane k))) ∩
          lineProductConstant k V (Plane k) X) := by
      rw [hpre, ← himg, ← himg, ← himg, Set.image_inter hh.injective]
    rw [hCfam, hinter, hpre, topologicalKrullDim_image_hom, topologicalKrullDim_image_hom,
      topologicalKrullDim_image_hom, ← IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph]
    exact h3
  · rw [hCfam, hfib]
    exact h4 i

end AlgebraicGeometry.ProjectiveLineBridge

end

module

public import StacksFrontier.AlgebraicGeometry.Cohomology.OpenImmersion.StructureSheafCohomologyPresheaf
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.HigherDirectImageBoundedness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective

/-!
# The vanishing of `H¹(𝒪)` descends to the base change along `Spec 𝒪_{X, x} ⟶ X`

Let `X` be a scheme with `H²(X, 𝒪_X) = 0`, let `x ∈ X` be a closed point, and let `g : X' ⟶ X`
be a proper morphism which is an isomorphism over `U = X ∖ {x}`. If `H¹(X', 𝒪_{X'}) = 0`, then
`H¹(Y, 𝒪_Y) = 0` for the base change `Y` of `g` along `Spec 𝒪_{X, x} ⟶ X`.

This is the step of the proof of [Stacks, Tag 0BG0] that rests on the first conclusion of
[Stacks, Tag 0AXF] and on flat base change ([Stacks, Tag 02KH]). It is proved here directly, by
Mayer–Vietoris rather than through the Leray sequence. Choose an affine open `V ∋ x`.

* On `X`, the sequence for `X = V ∪ U` and the vanishing of `H¹(V, 𝒪)` (Serre) and of
  `H²(X, 𝒪)` make `H¹(U, 𝒪) ⟶ H¹(U ∩ V, 𝒪)` surjective.
* `g` identifies `g⁻¹(U)` with `U`, compatibly with restriction to `g⁻¹(U ∩ V)`
  (`AlgebraicGeometry.Scheme.Hom.structureSheafCohomologyPresheafIso`), so
  `H¹(g⁻¹U, 𝒪) ⟶ H¹(g⁻¹(U ∩ V), 𝒪)` is surjective too.
* On `X'`, the sequence for `X' = g⁻¹V ∪ g⁻¹U` and `H¹(X', 𝒪) = 0` make
  `H¹(g⁻¹V) ⊕ H¹(g⁻¹U) ⟶ H¹(g⁻¹(U ∩ V))` injective; with the surjectivity this forces
  `H¹(g⁻¹V, 𝒪) = 0`.
* `Y` is the base change of `g⁻¹V ⟶ V` along the flat morphism of affine schemes
  `Spec 𝒪_{X, x} ⟶ V`, so `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isPullback`
  gives `H¹(Y, 𝒪_Y) = 0`.

When `X` is a modification of the spectrum of a two-dimensional Noetherian normal local domain,
its fibres have dimension at most one, so `H²(X, 𝒪_X) = 0` ([Stacks, Tag 02V7]).

## Main results

* `AlgebraicGeometry.subsingleton_cohomologyPresheaf_one_preimage_of_isIso_morphismRestrict`:
  the Mayer–Vietoris step, for any morphism of schemes which is an isomorphism over `U`.
* `AlgebraicGeometry.subsingleton_cohomologyPresheaf_two_top_of_isModification`:
  `H²(X, 𝒪_X) = 0` for a modification of a two-dimensional Noetherian normal local domain.
* `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isPullback_fromSpecStalk`: the
  descent of the vanishing to the base change along `Spec 𝒪_{X, x} ⟶ X`.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace AlgebraicGeometry

/-- Restriction maps of a presheaf on a preorder between equal pairs of objects are surjective
together. -/
theorem surjective_map_homOfLE_congr {T : Type*} [Preorder T] (F : Tᵒᵖ ⥤ AddCommGrpCat.{w})
    {a b a' b' : T} (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    Function.Surjective (F.map (homOfLE h).op) ↔ Function.Surjective (F.map (homOfLE h').op) := by
  subst ha hb
  rfl

/-- The category of abelian sheaves on the opens of a scheme has `Ext` groups. -/
private theorem hasExt_sheaf_opens_ab (Z : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) Ab.{u}) :=
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology Z) Ab.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  hasExt_of_enoughInjectives _

section MayerVietoris

variable {X X' : Scheme.{u}}
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X') Ab.{u})]

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X') Ab.{u})] in
/-- The image of an open of `U` under an inverse of `g ∣_ U` followed by the inclusion of
`g⁻¹ U` is the preimage under `g` of its image in `X`. -/
theorem image_inv_morphismRestrict_ι (g : X' ⟶ X) (U : X.Opens) [IsIso (g ∣_ U)]
    (W : U.toScheme.Opens) :
    (inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) ''ᵁ W = g ⁻¹ᵁ (U.ι ''ᵁ W) := by
  have hcomp : (inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) ≫ g = U.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    change U.ι w = g ((inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) w)
    rw [← Scheme.Hom.comp_apply, hcomp]
  · rintro y ⟨w, hw, hwy⟩
    have hyU : y ∈ g ⁻¹ᵁ U := by
      change g y ∈ U
      rw [← hwy]
      exact w.2
    obtain ⟨w', hw'⟩ : ∃ w', (inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) w' = y := by
      have hr : (inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).opensRange = g ⁻¹ᵁ U := by
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
      rwa [← hr] at hyU
    refine ⟨w', ?_, hw'⟩
    have e1 : U.ι w' = g y := by rw [← hw', ← Scheme.Hom.comp_apply, hcomp]
    rwa [U.ι.isOpenEmbedding.injective (e1.trans hwy.symm)]

/-- **The Mayer–Vietoris step.** Let `g : X' ⟶ X` be an isomorphism over an open `U`, and `V` an
open with `V ∪ U = X`. If `H¹(X', 𝒪) = 0`, `H¹(V, 𝒪) = 0` and `H²(X, 𝒪) = 0`, then
`H¹(g⁻¹ V, 𝒪) = 0`. -/
theorem subsingleton_cohomologyPresheaf_one_preimage_of_isIso_morphismRestrict (g : X' ⟶ X)
    (U V : X.Opens) (hUV : V ⊔ U = ⊤) [IsIso (g ∣_ U)]
    (hX' : Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op (⊤ : X'.Opens))))
    (hV : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op V)))
    (hX : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 2).obj
      (op (⊤ : X.Opens)))) :
    Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj (op (g ⁻¹ᵁ V))) := by
  let P := (structureAbelianSheaf X).cohomologyPresheaf.{u} 1
  let P' := (structureAbelianSheaf X').cohomologyPresheaf.{u} 1
  have hsurjX : Function.Surjective (P.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op) := by
    let S := Opens.mayerVietorisSquare V U
    have hseq := S.sequence_exact (structureAbelianSheaf X) 1 2 rfl
    have hX₄ : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 2).obj
        (op S.X₄)) := by
      change Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 2).obj
        (op (V ⊔ U)))
      rw [hUV]
      exact hX
    change Function.Surjective (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).map S.f₁₃.op)
    intro z
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 (hseq.exact 1) z
      (Subsingleton.elim (α := ((structureAbelianSheaf X).cohomologyPresheaf.{u} 2).obj
        (op S.X₄)) _ _)
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm
      |>.surjective y
    refine ⟨-y₂, ?_⟩
    have hy' := (S.fromBiprod_biprodIsoProd_inv_apply (structureAbelianSheaf X) y₁ y₂).symm.trans hy
    have hy₁ : y₁ = 0 := @Subsingleton.elim _ hV _ _
    rw [hy₁, map_zero, zero_sub] at hy'
    rw [← hy', map_neg]
  let h : U.toScheme ⟶ X' := inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι
  have := hasExt_sheaf_opens_ab U.toScheme
  let α := (U.ι.structureSheafCohomologyPresheafIso.{u} 1) ≪≫
    (h.structureSheafCohomologyPresheafIso.{u} 1).symm
  have hle : U.ι ⁻¹ᵁ V ≤ ⊤ := le_top
  have hsurjU : Function.Surjective
      (P.map (U.ι.opensFunctor.map (homOfLE hle)).op) := by
    have e₁ : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V ⊓ U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    have e₂ : U.ι ''ᵁ ⊤ = U := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    exact (surjective_map_homOfLE_congr P e₁ e₂ (U.ι.image_mono hle) inf_le_right).2 hsurjX
  have hsurjU' : Function.Surjective
      (P'.map (h.opensFunctor.map (homOfLE hle)).op) := by
    have hnat := α.hom.naturality (homOfLE hle).op
    have hcomp : (α.inv.app (op ⊤) ≫ P.map (U.ι.opensFunctor.map (homOfLE hle)).op) ≫
        α.hom.app (op (U.ι ⁻¹ᵁ V)) = P'.map (h.opensFunctor.map (homOfLE hle)).op := by
      rw [Category.assoc]
      exact (congrArg (fun k => α.inv.app (op ⊤) ≫ k) hnat).trans (α.inv_hom_id_app_assoc _ _)
    rw [← hcomp]
    exact ((ConcreteCategory.bijective_of_isIso (α.hom.app (op (U.ι ⁻¹ᵁ V)))).2.comp
      hsurjU).comp (ConcreteCategory.bijective_of_isIso (α.inv.app (op ⊤))).2
  have hsurjX' : Function.Surjective
      (P'.map (homOfLE (inf_le_right : g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U ≤ g ⁻¹ᵁ U)).op) := by
    have e₁ : h ''ᵁ (U.ι ⁻¹ᵁ V) = g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U := by
      rw [image_inv_morphismRestrict_ι, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, inf_comm]
    have e₂ : h ''ᵁ ⊤ = g ⁻¹ᵁ U := by
      rw [image_inv_morphismRestrict_ι, Scheme.Hom.image_top_eq_opensRange,
        Scheme.Opens.opensRange_ι]
    exact (surjective_map_homOfLE_congr P' e₁ e₂ (h.image_mono hle) inf_le_right).1 hsurjU'
  let S' := Opens.mayerVietorisSquare (g ⁻¹ᵁ V) (g ⁻¹ᵁ U)
  have hseq' := S'.sequence_exact (structureAbelianSheaf X') 0 1 rfl
  have hX'₄ : Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op S'.X₄)) := by
    change Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op (g ⁻¹ᵁ V ⊔ g ⁻¹ᵁ U)))
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
    exact hX'
  refine ⟨fun a a' => ?_⟩
  suffices hzero : ∀ a : P'.obj (op (g ⁻¹ᵁ V)), a = 0 by rw [hzero a, hzero a']
  intro a
  obtain ⟨b, hb⟩ := hsurjX' (P'.map (homOfLE (inf_le_left : g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U ≤ g ⁻¹ᵁ V)).op a)
  let y : ((structureAbelianSheaf X').H' 1 S'.X₂ ⊞ (structureAbelianSheaf X').H' 1 S'.X₃ :
      AddCommGrpCat) := (AddCommGrpCat.biprodIsoProd _ _).inv ⟨a, b⟩
  have hfrom : S'.fromBiprod (structureAbelianSheaf X') 1 y = 0 :=
    (S'.fromBiprod_biprodIsoProd_inv_apply (structureAbelianSheaf X') a b).trans
      (sub_eq_zero.2 hb.symm)
  obtain ⟨c, hc⟩ := (ShortComplex.ab_exact_iff _).1 (hseq'.exact 3) y hfrom
  have hc0 : c = 0 := Subsingleton.elim (α := ((structureAbelianSheaf X').cohomologyPresheaf.{u}
    1).obj (op S'.X₄)) _ _
  have hy : y = 0 := by rw [← hc, hc0, map_zero]
  have := congrArg (fun t => ((AddCommGrpCat.biprodIsoProd _ _).hom t).1) hy
  simp only [y, Iso.inv_hom_id_apply, map_zero] at this
  exact this

end MayerVietoris

section Modification

attribute [local instance 2000] HasDerivedCategory.standard

/-- **`H²(X, 𝒪_X) = 0` for a modification of a two-dimensional local ring.** Let `A` be a
two-dimensional Noetherian normal local domain and `f : X ⟶ Spec(A)` a modification with `X`
normal. The fibres of `f` have dimension at most one, so the cohomology of quasi-coherent modules
on `X` vanishes above degree one ([Stacks, Tag 02V7] over the affine Noetherian base). -/
theorem subsingleton_cohomologyPresheaf_two_top_of_isModification (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})] :
    Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 2).obj
      (op (⊤ : X.Opens))) := by
  let := hf.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  let : NoetherianSpace (f.fiber (IsLocalRing.closedPoint A)) :=
    (f.fiberHomeo _).isEmbedding.noetherianSpace
  let : Fintype {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))} :=
    (NoetherianSpace.finite_irreducibleComponents
      (α := f.fiber (IsLocalRing.closedPoint A))).fintype
  let S : VanishingSituation.{u} :=
    { A := A
      dimension_two := hdim
      X := X
      f := f
      modification := hf
      numberOfComponents := Fintype.card _
      components := (Fintype.equivFin _).symm }
  let T : SemistableReduction.TwoModifications.{u} :=
    { situation := S
      X' := X
      g := 𝟙 X
      modification' := by
        change IsModification (𝟙 X ≫ f)
        rw [Category.id_comp]
        exact hf
      normal := ‹IsNormal X› }
  have hfib : ∀ s : Spec (.of A), topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro s
    have h : topologicalKrullDim ((𝟙 X ≫ f).fiber s) ≤ 1 := T.topologicalKrullDim_fiber_f'_le_one s
    rw [Category.id_comp] at h
    simpa using h
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have h := open Stacks.AlgebraicGeometry.FibreDimension in
    isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent f hfib
      (SheafOfModules.unit X.ringCatSheaf) (p := 2) (by norm_num)
  replace h :=
    (Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup X
      _ 2).1 h
  exact AddCommGrpCat.subsingleton_of_isZero
    ((Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf ⊤ _ 2).1 h)

end Modification

open GlueingNearPoint in
/-- **The vanishing of `H¹(𝒪)` descends to the base change along `Spec 𝒪_{X, x} ⟶ X`.** Let `A` be
a two-dimensional Noetherian normal local domain, `f : X ⟶ Spec(A)` a modification with `X`
normal and `x ∈ X` a closed point. Let `g : X' ⟶ X` be proper and an isomorphism over `X ∖ {x}`,
and `Y` its base change along `Spec 𝒪_{X, x} ⟶ X`. If `H¹(X', 𝒪_{X'}) = 0` then
`H¹(Y, 𝒪_Y) = 0`.

This replaces, for the morphisms the proof of [Stacks, Tag 0BG0] meets, the first conclusion of
[Stacks, Tag 0AXF] together with flat base change ([Stacks, Tag 02KH]). -/
theorem isZeroFirstStructureSheafCohomology_of_isPullback_fromSpecStalk (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2) {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A))
    (hf : IsModification f) (x : X) (hx : IsClosed ({x} : Set X)) {X' Y : Scheme.{u}}
    (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x)) (q : Y ⟶ X')
    (hsq : IsPullback q p g (X.fromSpecStalk x)) (hg : IsProper g)
    (hiso : IsIso ((Over.pullback (puncturedOpen hx).ι).obj (Over.mk g)).hom)
    (hX' : IsZeroFirstStructureSheafCohomology X') :
    IsZeroFirstStructureSheafCohomology Y := by
  have := hasExt_sheaf_opens_ab X
  have := hasExt_sheaf_opens_ab X'
  set U := puncturedOpen hx
  have : IsIso (g ∣_ U) := by
    have : IsIso (pullback.snd g U.ι) := hiso
    unfold morphismRestrict
    infer_instance
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have hUV : V ⊔ U = ⊤ := by
    refine top_le_iff.mp fun y _ => ?_
    by_cases hy : y = x
    · exact Or.inl (hy ▸ hxV)
    · exact Or.inr hy
  have hX'top : Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op (⊤ : X'.Opens))) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top _ 1).1 hX'
  have hVvan : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op V)) :=
    AddCommGrpCat.subsingleton_of_isZero
      ((Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf V _ 1).1
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X
          (SheafOfModules.unit X.ringCatSheaf) V hV 1 one_pos))
  have hpre := subsingleton_cohomologyPresheaf_one_preimage_of_isIso_morphismRestrict g U V hUV
    hX'top hVvan (subsingleton_cohomologyPresheaf_two_top_of_isModification A hdim f hf)
  have hW : IsZeroFirstStructureSheafCohomology (g ⁻¹ᵁ V).toScheme := by
    have := hasExt_sheaf_opens_ab (g ⁻¹ᵁ V).toScheme
    refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top _ 1).2 ?_
    have hs : Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
        (op ((g ⁻¹ᵁ V).ι ''ᵁ ⊤))) := by
      rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    exact ((((g ⁻¹ᵁ V).ι.structureSheafCohomologyPresheafIso.{u} 1).app
      (op ⊤)).addCommGroupIsoToAddEquiv.symm.toEquiv.subsingleton)
  have hright := (isPullback_morphismRestrict g V).flip
  have hw : q ≫ g = (p ≫ V.fromSpecStalkOfMem x hxV) ≫ V.ι := by
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact hsq.w
  let q' : Y ⟶ (g ⁻¹ᵁ V).toScheme := hright.lift q (p ≫ V.fromSpecStalkOfMem x hxV) hw
  have hbig : IsPullback (q' ≫ (g ⁻¹ᵁ V).ι) p g (V.fromSpecStalkOfMem x hxV ≫ V.ι) := by
    rwa [hright.lift_fst, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hpb : IsPullback q' p (g ∣_ V) (V.fromSpecStalkOfMem x hxV) :=
    IsPullback.of_right hbig (hright.lift_snd _ _ _) hright
  have : IsAffine V.toScheme := hV
  have : Flat (V.fromSpecStalkOfMem x hxV) := by
    have hsq' : IsPullback (𝟙 _) (V.fromSpecStalkOfMem x hxV)
        (V.fromSpecStalkOfMem x hxV ≫ V.ι) V.ι :=
      IsPullback.of_isLimit' ⟨by rw [Category.id_comp]⟩
        (PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
          (fun s => by rw [← cancel_mono V.ι, Category.assoc]; exact s.condition)
          (fun s m h₁ _ => by rw [← h₁, Category.comp_id]))
    have hflat : Flat (V.fromSpecStalkOfMem x hxV ≫ V.ι) := by
      rw [Scheme.Opens.fromSpecStalkOfMem_ι]
      exact flat_fromSpecStalk X x
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hsq' hflat
  have : IsProper g := hg
  exact isZeroFirstStructureSheafCohomology_of_isPullback hpb hW

end AlgebraicGeometry

end

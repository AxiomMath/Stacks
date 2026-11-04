module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# Sections of a quasi-coherent module on an affine algebraic space

Let `V` be an affine algebraic space, `e : V ≅ yoneda T₀` with `T₀` affine.  The chart `e⁻¹` is a
*terminal* object of the small étale site of `V`: a chart `T ⟶ V` factors uniquely through it,
by the Yoneda lemma.  So a section of an `𝒪_V`-module over that chart is the same as a global
section.  For a quasi-coherent module `F`, Descent 03DX (2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`) says that over an
affine chart `A` the sections are the base change of the sections over the terminal chart, so
every section over `A` is a finite `𝒪(A)`-linear combination of restrictions of global sections.

## Main results

* `AlgebraicGeometry.Space.exists_sum_smul_sections_eval_of_isAffineSpace`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every chart maps to the chart `AlgebraicGeometry.Space.isoChart` of the inverse
isomorphism. -/
noncomputable def toIsoChartSymm {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS}
    (e : F ≅ yoneda.obj T₀) (Y : SmallEtale B S hS F) : Y ⟶ isoChart B S hS e.symm :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (Y.1.hom ≫ e.hom)) (by
    change yoneda.map (yoneda.preimage (Y.1.hom ≫ e.hom)) ≫ e.inv = Y.1.hom
    simp))

/-- Any two morphisms to the chart `AlgebraicGeometry.Space.isoChart` agree. -/
theorem hom_isoChart_ext {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS}
    (e : F ≅ yoneda.obj T₀) {Y : SmallEtale B S hS F} (a b : Y ⟶ isoChart B S hS e.symm) :
    a = b := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply yoneda.map_injective
  exact (cancel_mono e.inv).1
    ((CostructuredArrow.w a.hom).trans (CostructuredArrow.w b.hom).symm)

/-- Restricting a section over the chart `AlgebraicGeometry.Space.isoChart` to the charts is
compatible with the restrictions between them. -/
theorem isoChart_map_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {T₀ : BigFppfOver B S hS} (e : F ≅ yoneda.obj T₀)
    (G : Modules.{u, u} B S hS F hF) (x : G.val.obj (op (isoChart B S hS e.symm)))
    {Y Z : SmallEtale B S hS F} (f : Z ⟶ Y) :
    G.val.map f.op (G.val.map (toIsoChartSymm B S hS e Y).op x) =
      G.val.map (toIsoChartSymm B S hS e Z).op x := by
  have h2 : (toIsoChartSymm B S hS e Y).op ≫ f.op = (toIsoChartSymm B S hS e Z).op :=
    Quiver.Hom.unop_inj (hom_isoChart_ext B S hS e _ _)
  have e1 : G.val.map ((toIsoChartSymm B S hS e Y).op ≫ f.op) x =
      G.val.map f.op (G.val.map (toIsoChartSymm B S hS e Y).op x) :=
    PresheafOfModules.map_comp_apply G.val _ _ x
  exact e1.symm.trans (PresheafOfModules.congr_map_apply G.val h2 x)

/-- The global section of an `𝒪_F`-module determined by a section over the chart
`AlgebraicGeometry.Space.isoChart`. -/
noncomputable def isoChartSymmSection {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {T₀ : BigFppfOver B S hS} (e : F ≅ yoneda.obj T₀)
    (G : Modules.{u, u} B S hS F hF) (x : G.val.obj (op (isoChart B S hS e.symm))) :
    G.val.sections :=
  PresheafOfModules.sectionsMk (fun Y => G.val.map (toIsoChartSymm B S hS e Y.unop).op x)
    (fun _ _ f => isoChart_map_map B S hS hF e G x f.unop)

/-- **Sections over an affine chart of an affine algebraic space.**  A section of a
quasi-coherent module over an affine chart of an affine algebraic space is a finite linear
combination of restrictions of global sections. -/
theorem exists_sum_smul_sections_eval_of_isAffineSpace {V : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (F : Modules.{u, u} B S hS V.1 V.2)
    (hF : F.IsQuasicoherentOnSite) (A : SmallEtale B S hS V.1)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS V.1).obj A)))
    (y : F.val.obj (op A)) :
    ∃ (n : ℕ) (m : Fin n → F.val.sections)
      (a : Fin n → (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V.1 V.2).O).obj.obj (op A)),
      y = ∑ i, a i • (m i).eval (op A) := by
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hV
  have hcart := (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS V.1 V.2 F).1 hF
  set f := toIsoChartSymm B S hS e A
  have hbij := hcart (isoChart B S hS e.symm) A hT₀ hA f
  have hspan := (chartBaseChange_surjective_iff_span_eq_top F f).1 hbij.2
  have hy : y ∈ Submodule.span (chartRing B S hS V.1 V.2 A)
      (Set.range fun x : F.val.obj (op (isoChart B S hS e.symm)) => chartRestrictLinear F f x) := by
    rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hy
  choose x hx using fun i => (g i).2
  refine ⟨n, fun i => isoChartSymmSection B S hS V.2 e F (x i), c, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i]
  rfl

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.SheafSubquotient
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Affine
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.AffineTopSectionsLe
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPointReading
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceChartIdealQcoh
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# A global finite type submodule of `𝒜_d` cutting out a closed subspace on a chart

Let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Situation 0849 constructed in
Stacks 084A–084B over a quasi-compact and quasi-separated algebraic space `X`, `i : Z ⟶ P` a
closed immersion with `π` quasi-compact, and `f : T ⟶ X` an affine étale scheme point.  Over
`T` the fibre `Z_T ⊆ Proj_T(f^*𝒜)` has its equations; Stacks 0803 produces a quasi-coherent
finite type `ℱ' ⊆ (f^*𝒜)_d` of equations of `Z_T`.  This file carries out the globalization step
of the proof of Stacks 085N: there is a quasi-coherent finite type `𝒪_X`-submodule `ℱ ⊆ 𝒜_d`
such that

  `ℱ' ⊆ 𝒢 ⊆ ℐ_d(Z_T)`,

where `𝒢 ⊆ (f^*𝒜)_d` is the image of `f^*ℱ` and `ℐ_d(Z_T)` the degree `d` equations of `Z_T`.
The submodule `ℱ` is found inside the degree `d` part `ℐ_d ⊆ 𝒜_d` of the graded ideal of `Z`
(`AlgebraicGeometry.Space.RelativeProjSituation.chartIdeal`, quasi-coherent by
`AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_chartIdeal`) by the
globalization of finite type submodules on quasi-compact quasi-separated algebraic spaces
(Stacks 0829, `AlgebraicGeometry.Space.exists_isFiniteType_submodule_mem_of_qcqs`), applied to
finitely many sections of `ℐ_d` over `T` whose readings generate `ℱ'`.

## Main results

* `AlgebraicGeometry.exists_app_top_eq_of_mem_imageSubmodule`: over an affine scheme a global
  section of the image of a morphism of quasi-coherent modules comes from a global section;
  `AlgebraicGeometry.obj_top_le_of_span_eq_top`: global sections are compared on generators.
* `AlgebraicGeometry.Space.bijective_modulePullbackUnitSection_selfOpensChartDiagram_top`: over an
  affine étale chart `V = (T, v)` the global sections of `v^*G` are the unit sections of `G(V)`,
  for `G` quasi-coherent.
* `AlgebraicGeometry.Space.modulePullbackUnitSection_heq_of_comp_eqToHom`: the pullback of a
  morphism carries unit sections to unit sections.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_and_isFiniteType_monoRangeSubmodule`: the range
  of a monomorphism out of a quasi-coherent module of finite type is such a submodule.
* `AlgebraicGeometry.Space.mem_of_heq_zariskiImage` and
  `AlgebraicGeometry.Space.exists_heq_of_mem_zariskiImage`: the global sections of a Zariski
  image over an affine scheme point are the values on global sections.
* `RelativeProjSituation.mem_pointZariskiImageSubmodule_of_heq_chartOpenReading` and
  `RelativeProjSituation.exists_heq_chartOpenReading_of_mem_pointZariskiImageSubmodule`: the
  global sections of the image `𝒢` of `v^*ℱ` are the readings of the sections of `ℱ` over `V`.
* `RelativeProjSituation.exists_finset_le_pointZariskiImageSubmodule` (`ℱ' ⊆ 𝒢` from finitely
  many generators) and `RelativeProjSituation.pointZariskiImageSubmodule_le_twistKer`
  (`𝒢 ⊆ ℐ_d(Z_T)`).
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_finiteType_le_pointZariskiImageSubmodule`:
  **the globalization step**: `ℱ' ⊆ 𝒢 ⊆ ℐ_d(Z_T)` for a quasi-coherent finite type `ℱ ⊆ 𝒜_d`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsAffine X]

/-- **Over an affine scheme a global section of the image of a morphism of quasi-coherent
modules is the image of a global section**: the corestriction to the image is an epimorphism of
quasi-coherent modules, surjective on the sections over the affine open `⊤`. -/
theorem exists_app_top_eq_of_mem_imageSubmodule {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (p : M ⟶ N) {x : Γ(N, ⊤)}
    (hx : x ∈ (imageSubmodule p).toSubmodule.obj (op ⊤)) : ∃ c : Γ(M, ⊤), p.app ⊤ c = x := by
  have : ((imageSubmodule p).toSheafOfModules : X.Modules).IsQuasicoherent :=
    isQuasicoherent_imageSubmodule p
  obtain ⟨c, hc⟩ := surjective_app_of_epi_of_isAffineOpen (toImageSubmodule p)
    (isAffineOpen_top X) ⟨x, hx⟩
  refine ⟨c, ?_⟩
  have h := congrArg (fun χ : M ⟶ N => χ.app ⊤ c) (toImageSubmodule_comp_subι p)
  exact h.symm.trans (congrArg Subtype.val hc)

omit [IsAffine X] in
/-- **The global sections of a submodule `A` lie in those of `B` as soon as a set generating them
does.** -/
theorem obj_top_le_of_span_eq_top {M : X.Modules} {A B : M.Submodule}
    (S : Set Γ((show X.Modules from A.toSheafOfModules), ⊤))
    (hS : Submodule.span Γ(X, ⊤) S = ⊤)
    (h : ∀ w ∈ S, A.ι.val.app (op ⊤) w ∈ B.obj (op ⊤)) : A.obj (op ⊤) ≤ B.obj (op ⊤) := by
  have key : ∀ w ∈ Submodule.span Γ(X, ⊤) S, A.ι.val.app (op ⊤) w ∈ B.obj (op ⊤) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact (map_zero (A.ι.val.app (op ⊤)).hom).symm ▸ Submodule.zero_mem _
    | add x y _ _ hx hy =>
      exact (map_add (A.ι.val.app (op ⊤)).hom x y).symm ▸ Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      exact ((A.ι.val.app (op ⊤)).hom.map_smul r x).symm ▸ Submodule.smul_mem _ r hx
  intro y hy
  obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (A.ι.val.app (op ⊤)).hom :=
    (range_submodule_ι_app A ⊤).symm ▸ hy
  exact key z (hS ▸ Submodule.mem_top)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Over an affine étale chart `V = (T, v)` the global sections of `v^*G` are the unit sections
of `G(V)`**, for `G` quasi-coherent: the unit section is the base-change comparison
`Γ(T) ⊗_{𝒪(V)} G(V) ⟶ Γ(T, v^*G)` of Descent 03DX (2), whose coefficient map is bijective,
precomposed with `g ↦ 1 ⊗ g`. -/
theorem bijective_modulePullbackUnitSection_selfOpensChartDiagram_top (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) :
    Function.Bijective (modulePullbackUnitSection B S hS (pointHom V.1.hom) G
      (selfOpensChartDiagram V ⊤)) := by
  let := chartDiagramAlgebra B S hS (pointHom V.1.hom) (selfOpensChartDiagram V ⊤)
  have hbc := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS
    (pointHom V.1.hom) G hG (selfOpensChartDiagram V ⊤)
    (isAffine_selfOpensTop V.1.left) hV
  have h1 := TensorProduct.bijective_one_tmul_of_bijective_algebraMap
    (R := chartRing B S hS X.1 X.2 (selfOpensChartDiagram V ⊤).V)
    (A := chartRing B S hS (yoneda.obj V.1.left) (isAlgebraicSpace_yoneda B S hS V.1.left)
      (selfOpensChartDiagram V ⊤).U)
    (M := G.val.obj (op (selfOpensChartDiagram V ⊤).V))
    (bijective_chartDiagramPullback_selfOpensChartDiagram_top V)
  have e : modulePullbackUnitSection B S hS (pointHom V.1.hom) G (selfOpensChartDiagram V ⊤) =
      modulePullbackChartBaseChange B S hS (pointHom V.1.hom) G
        (selfOpensChartDiagram V ⊤) ∘ fun m => (1 : chartRing B S hS (yoneda.obj V.1.left)
          (isAlgebraicSpace_yoneda B S hS V.1.left) (selfOpensChartDiagram V ⊤).U) ⊗ₜ[_] m := by
    funext m
    refine (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS
      (pointHom V.1.hom) G (selfOpensChartDiagram V ⊤) m).trans ?_
    exact ((modulePullbackChartBaseChange_tmul B S hS (pointHom V.1.hom) G
      (selfOpensChartDiagram V ⊤) 1 m).trans (one_smul _ _)).symm
  rw [e]
  exact hbc.comp h1

/-- **The pullback of a morphism carries unit sections to unit sections**, for a morphism
`φ : f^*M ⟶ E` equal to `f^*ψ` up to an identification `E = f^*N`: `φ` carries the unit section of
`g ∈ M(V)` to the unit section of `ψ(g)`, up to that identification.  This is the naturality of
the unit of Stacks 03D7 in the module. -/
theorem modulePullbackUnitSection_heq_of_comp_eqToHom {X' : AlgebraicSpaces B S hS}
    (f : X' ⟶ X) (d : ChartDiagram B S hS X'.1 X.1 f.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : M ⟶ N) {E : Modules.{u, u} B S hS X'.1 X'.2} (φ : (modulePullback B S hS f).obj M ⟶ E)
    (h : E = (modulePullback B S hS f).obj N)
    (hφ : φ ≫ eqToHom h = (modulePullback B S hS f).map ψ) (g : M.val.obj (op d.V)) :
    HEq (φ.val.app (op d.U) (modulePullbackUnitSection B S hS f M d g))
      (modulePullbackUnitSection B S hS f N d (ψ.val.app (op d.V) g)) := by
  subst h
  rw [eqToHom_refl, Category.comp_id] at hφ
  subst hφ
  exact heq_of_eq (modulePullbackUnitSection_naturality_module B S hS f ψ d g).symm

/-- The reading of a section over an étale chart is its unit section, in the spelling of the
pullback of modules (`AlgebraicGeometry.Space.chartOpenReading` is that unit section, read as a
section of the Zariski reading of the pulled-back algebra). -/
theorem chartOpenReading_heq_modulePullbackUnitSection
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1) (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) (n : ℤ)
    (a : (A.piece n).val.obj (op V)) :
    HEq (chartOpenReading A V O n a)
      (modulePullbackUnitSection B S hS (pointHom V.1.hom) (A.piece n)
        (selfOpensChartDiagram V O) a) :=
  HEq.rfl

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **The range of a monomorphism out of a quasi-coherent module of finite type is a
quasi-coherent submodule of finite type** of the target: it is isomorphic to the source. -/
theorem isQuasicoherentOnSite_and_isFiniteType_monoRangeSubmodule
    {G P : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ P) [Mono φ] (hq : G.IsQuasicoherentOnSite)
    (hf : G.IsFiniteTypeOnSite) :
    SheafOfModules.IsQuasicoherentOnSite
        (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule φ).toSheafOfModules ∧
      SheafOfModules.IsFiniteType
        (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule φ).toSheafOfModules :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso φ) hq,
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
      (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso φ)
      (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hf)⟩

section ZariskiImage

variable (T : BigFppfOver B S hS)
  {G N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)} (φ : G ⟶ N)
  {M : ((BigFppfOver.toScheme B S hS).obj T).Modules}
  (hM : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N :
    ((BigFppfOver.toScheme B S hS).obj T).Modules) = M)
  {K : M.Submodule}
  (hK : HEq K (AlgebraicGeometry.imageSubmodule
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map φ)))

include hM hK

/-- A global section of a module `M` on `T` which is, through an identification of `M` with the
Zariski reading of `N`, a value of `φ : G ⟶ N`, lies in any submodule `K` identified with the
Zariski image of `φ`. -/
theorem mem_of_heq_zariskiImage {x : M.val.obj (op ⊤)}
    (c : G.val.obj (op ((selfOpensFunctor B S hS T).obj ⊤)))
    (hx : HEq x (φ.val.app (op ((selfOpensFunctor B S hS T).obj ⊤)) c)) :
    x ∈ K.toSubmodule.obj (op ⊤) := by
  subst hM
  obtain rfl := eq_of_heq hK
  obtain rfl := eq_of_heq hx
  refine (AlgebraicGeometry.mem_kernelSubmodule_iff _ ⊤ _).2 ?_
  exact congrArg (fun χ => χ.val.app (op ⊤) c)
    (cokernel.condition (C := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map φ))

/-- **Over an affine scheme point, a global section of the Zariski image of `φ : G ⟶ N` is a
value of `φ`** on a global section, for `G` and `N` quasi-coherent; stated for any submodule `K`
identified with that image. -/
theorem exists_heq_of_mem_zariskiImage (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hG : G.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) {x : M.val.obj (op ⊤)}
    (hx : x ∈ K.toSubmodule.obj (op ⊤)) :
    ∃ c : G.val.obj (op ((selfOpensFunctor B S hS T).obj ⊤)),
      HEq x (φ.val.app (op ((selfOpensFunctor B S hS T).obj ⊤)) c) := by
  subst hM
  obtain rfl := eq_of_heq hK
  obtain ⟨c, hc⟩ := @exists_app_top_eq_of_mem_imageSubmodule _ hT _ _
    (isQuasicoherent_zariskiReading_piece T G hG) (isQuasicoherent_zariskiReading_piece T N hN)
    _ _ hx
  exact ⟨c, heq_of_eq hc.symm⟩

end ZariskiImage

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable (s : RelativeProjSituation.{u, u})
  (V : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1)

/-- The chart diagram `⊤ ⊆ T ⟶ V` of an étale chart, spelled through `s.site`. -/
local notation "𝒹" => selfOpensChartDiagram (B := s.site) (S := s.base) (hS := s.containsBase)
  (X := s.space) V ⊤

/-- **The pullback `v^*ℱ ⟶ (v^*𝒜)_d` carries the unit section of `g ∈ ℱ(V)` to the reading of
`g`** over an étale chart `V = (T, v)`, up to the two spellings of the sections of `(v^*𝒜)_d`. -/
theorem chartOpenReading_heq_pointImageMap_app_unitSection {d : ℤ}
    (ℱ : (s.algebra.piece d).Submodule) (g : ℱ.toSheafOfModules.val.obj (op V)) :
    HEq (chartOpenReading s.shrink.algebra V ⊤ d
        ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op V) g))
      ((s.pointImageMap (T := V.1.left) V.1.hom ℱ).val.app (op (𝒹).U)
        (modulePullbackUnitSection s.site s.base s.containsBase (pointHom (X := s.space) V.1.hom)
          ℱ.toSheafOfModules 𝒹 g)) := by
  have e1 := modulePullbackUnitSection_heq_of_comp_eqToHom (pointHom (X := s.space) V.1.hom) 𝒹
    (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv) (s.pointImageMap (T := V.1.left) V.1.hom ℱ)
    (s.etalePointAlgebra_shrink_piece_eq (T := V.1.left) V.1.hom d)
    (s.pointImageMap_comp_eqToHom (T := V.1.left) V.1.hom ℱ) g
  have e3 : HEq (modulePullbackUnitSection s.site s.base s.containsBase
      (pointHom (X := s.space) V.1.hom) (s.smallAlgebra.piece d) 𝒹
        ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op (𝒹).V) g))
      (modulePullbackUnitSection s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := s.shrink.space) V.1.hom) (s.shrink.algebra.piece d)
        (selfOpensChartDiagram V ⊤)
        ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op V) g)) := HEq.rfl
  exact ((chartOpenReading_heq_modulePullbackUnitSection s.shrink.algebra V ⊤ d
    ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op V) g)).trans e3.symm).trans e1.symm

/-- **The reading of a section of `ℱ` over an étale chart `V = (T, v)` lies in the image `𝒢` of
`v^*ℱ`**: a global section of `(v^*𝒜)_d` which is that reading, up to the two spellings of the
sections, lies in `𝒢`. -/
theorem mem_pointZariskiImageSubmodule_of_heq_chartOpenReading {d : ℤ}
    (ℱ : (s.algebra.piece d).Submodule) (g : ℱ.toSheafOfModules.val.obj (op V))
    {x : ((s.shrink.pointAlgebra V.1.left V.1.hom).piece d).val.obj (op ⊤)}
    (hx : HEq x (chartOpenReading s.shrink.algebra V ⊤ d
        ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op V) g))) :
    x ∈ (s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ).toSubmodule.obj (op ⊤) :=
  mem_of_heq_zariskiImage (B := s.site) (S := s.base) (hS := s.containsBase) V.1.left
    (s.pointImageMap (T := V.1.left) V.1.hom ℱ)
    (s.pointAlgebra_shrink_piece_eq (T := V.1.left) V.1.hom d)
    (s.pointZariskiImageSubmodule_heq (T := V.1.left) (f := V.1.hom) ℱ)
    (modulePullbackUnitSection s.site s.base s.containsBase (pointHom (X := s.space) V.1.hom)
      ℱ.toSheafOfModules 𝒹 g)
    (hx.trans (s.chartOpenReading_heq_pointImageMap_app_unitSection V ℱ g))

/-- **Over an affine étale chart `V = (T, v)`, the global sections of the image `𝒢` of `v^*ℱ`
are the readings of the sections of `ℱ` over `V`**, for `ℱ` quasi-coherent, up to the two
spellings of the sections of `(v^*𝒜)_d`. -/
theorem exists_heq_chartOpenReading_of_mem_pointZariskiImageSubmodule
    (hV : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left)) {d : ℤ}
    (ℱ : (s.algebra.piece d).Submodule) (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    {x : ((s.shrink.pointAlgebra V.1.left V.1.hom).piece d).val.obj (op ⊤)}
    (hx : x ∈ (s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ).toSubmodule.obj
      (op ⊤)) :
    ∃ g : ℱ.toSheafOfModules.val.obj (op V),
      HEq x (chartOpenReading s.shrink.algebra V ⊤ d
        ((ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv).val.app (op V) g)) := by
  obtain ⟨c, hc⟩ := exists_heq_of_mem_zariskiImage (B := s.site) (S := s.base)
    (hS := s.containsBase) V.1.left (s.pointImageMap (T := V.1.left) V.1.hom ℱ)
    (s.pointAlgebra_shrink_piece_eq (T := V.1.left) V.1.hom d)
    (s.pointZariskiImageSubmodule_heq (T := V.1.left) (f := V.1.hom) ℱ) hV
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base
      s.containsBase (pointHom (X := s.space) V.1.hom) _ hℱ)
    (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
      V.1.hom d) hx
  obtain ⟨g, rfl⟩ := (bijective_modulePullbackUnitSection_selfOpensChartDiagram_top (B := s.site)
    (X := s.space) V hV ℱ.toSheafOfModules hℱ).2 c
  exact ⟨g, hc.trans (s.chartOpenReading_heq_pointImageMap_app_unitSection V ℱ g).symm⟩

/-- **`ℱ' ⊆ 𝒢` from generators**: over an affine étale chart `V = (T, v)`, a quasi-coherent
`ℱ' ⊆ (v^*𝒜)_d` lies in the image `𝒢` of `v^*ℱ` as soon as a set generating its global sections
consists of readings of sections of `ℱ` over `V`. -/
theorem le_pointZariskiImageSubmodule_of_span_eq_top
    (hV : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left)) {d : ℤ}
    (ℱ' : ((s.shrink.pointAlgebra V.1.left V.1.hom).piece d).Submodule)
    (hℱ'q : ℱ'.toSheafOfModules.IsQuasicoherent) (ℱ : (s.algebra.piece d).Submodule)
    (gens : Set Γ((show ((BigFppfOver.toScheme s.shrink.site s.shrink.base
      s.shrink.containsBase).obj V.1.left).Modules from ℱ'.toSheafOfModules), ⊤))
    (hgens : Submodule.span Γ(((BigFppfOver.toScheme s.shrink.site s.shrink.base
      s.shrink.containsBase).obj V.1.left), ⊤) gens = ⊤)
    (h : ∀ w ∈ gens, ∃ b ∈ ℱ.obj (op V),
      chartOpenReading s.shrink.algebra V ⊤ d
        ((s.smallAlgebraPieceIso d).inv.val.app (op V) b) = ℱ'.ι.val.app (op ⊤) w) :
    ℱ' ≤ s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ := by
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left) := hV
  have := hℱ'q
  refine Scheme.Modules.submodule_le_of_obj_top_le
    (obj_top_le_of_span_eq_top gens hgens fun w hw => ?_)
  obtain ⟨b, hb, hg⟩ := h w hw
  exact s.mem_pointZariskiImageSubmodule_of_heq_chartOpenReading V ℱ ⟨b, hb⟩ (heq_of_eq hg).symm

/-- **Finitely many generators of `ℱ'`**: over an affine étale chart `V = (T, v)`, a quasi-coherent
finite type `ℱ' ⊆ (v^*𝒜)_d` has a finite set of global sections such that `ℱ'` lies in the image
`𝒢` of `v^*ℱ` for every `ℱ` whose sections over `V` read to all of them. -/
theorem exists_finset_le_pointZariskiImageSubmodule
    (hV : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left)) {d : ℤ}
    (ℱ' : ((s.shrink.pointAlgebra V.1.left V.1.hom).piece d).Submodule)
    (hℱ'q : ℱ'.toSheafOfModules.IsQuasicoherent)
    (hℱ'f : SheafOfModules.IsFiniteType.{u, u, u} ℱ'.toSheafOfModules) :
    ∃ gens : Finset (((s.shrink.pointAlgebra V.1.left V.1.hom).piece d).val.obj (op ⊤)),
      (∀ w ∈ gens, w ∈ ℱ'.obj (op ⊤)) ∧
        ∀ ℱ : (s.algebra.piece d).Submodule, (∀ w ∈ gens, ∃ b ∈ ℱ.obj (op V),
          chartOpenReading s.shrink.algebra V ⊤ d
            ((s.smallAlgebraPieceIso d).inv.val.app (op V) b) = w) →
          ℱ' ≤ s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ := by
  classical
  have : IsAffine ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj
    V.1.left) := hV
  have hfin :=
    @Stacks.AlgebraicGeometry.FiniteTypeSubmodule.module_finite_sections_of_isFiniteType_restrict
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj V.1.left)
      (show ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj
        V.1.left).Modules from ℱ'.toSheafOfModules) hℱ'q ⊤ (isAffineOpen_top _)
      (@Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict _ _ (⊤ : Scheme.Opens _).ι _
        ℱ'.toSheafOfModules hℱ'f)
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨S.image (fun x => ℱ'.ι.val.app (op ⊤) x), fun w hw => ?_, fun ℱ h => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hw
    exact x.2
  · exact s.le_pointZariskiImageSubmodule_of_span_eq_top V hV ℱ' hℱ'q ℱ (S : Set _) hS
      fun x hx => h _ (Finset.mem_image_of_mem _ hx)

/-- **`𝒢 ⊆ ℐ_d(Z_T)`**: over an affine étale chart `V = (T, v)`, the image `𝒢` of `v^*ℱ` consists
of equations of the fibre `Z_T` as soon as `ℱ` is quasi-coherent and its sections over `V` are
carried into `ℐ_d` by the comparison of the re-presented algebra. -/
theorem pointZariskiImageSubmodule_le_twistKer
    {Z : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {i : Z ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    (hV : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left))
    [_root_.AlgebraicGeometry.IsClosedImmersion (s.fibreClosedImmersion hi V.1.left V.1.hom)]
    [QuasiCompact (relativeProj (s.shrink.pointAlgebra V.1.left V.1.hom)).toBase] {d : ℕ}
    (ℱ : (s.algebra.piece (d : ℤ)).Submodule) (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    (h : ∀ b ∈ ℱ.obj (op V), s.IsChartEquation hi d V
      ((s.smallAlgebraPieceIso (d : ℤ)).inv.val.app (op V) b)) :
    s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ ≤
      (twistKerGradedIdeal (s.shrink.pointAlgebra V.1.left V.1.hom)
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (s.fibreClosedImmersion hi V.1.left V.1.hom)).piece (d : ℤ) := by
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left) := hV
  have := s.isQuasicoherent_pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ hℱ
  refine Scheme.Modules.submodule_le_of_obj_top_le fun x hx => ?_
  obtain ⟨g, hg⟩ := s.exists_heq_chartOpenReading_of_mem_pointZariskiImageSubmodule V hV ℱ hℱ hx
  refine (twistEquationSection_eq_zero_iff _ _ d x).1 ?_
  exact (congrArg (twistEquationSection (s.shrink.pointAlgebra V.1.left V.1.hom)
    (s.fibreClosedImmersion hi V.1.left V.1.hom) d) (eq_of_heq hg)).trans
    (IsChartEquation.twistEquationSection_eq_zero s hi hV (h g.1 g.2))

omit V in
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **The globalization step of Stacks 085N.**  Let `X` be quasi-compact and quasi-separated,
`i : Z ⟶ P` a closed immersion with `π` quasi-compact, `V = (T, v)` an affine étale chart of `X`
and `ℱ' ⊆ (v^*𝒜)_d` a quasi-coherent finite type submodule of equations of the fibre `Z_T`.  Then
there is a quasi-coherent finite type `𝒪_X`-submodule `ℱ ⊆ 𝒜_d` with
`ℱ' ⊆ 𝒢 ⊆ ℐ_d(Z_T)`, where `𝒢` is the image of `v^*ℱ`.

The readings of finitely many generators of `ℱ'` over `T` are sections of the degree `d` part
`ℐ_d ⊆ 𝒜_d` of the graded ideal of `Z` over `V`
(`AlgebraicGeometry.Space.RelativeProjSituation.isChartEquation_of_twistEquationSection_eq_zero`);
`ℐ_d` is quasi-coherent, so Stacks 0829 gives a quasi-coherent finite type `ℱ ⊆ ℐ_d` containing
them; `ℱ'` lies in `𝒢` because its generators do, and `𝒢` consists of equations because its
global sections are readings of sections of `ℱ ⊆ ℐ_d`. -/
theorem exists_finiteType_le_pointZariskiImageSubmodule
    (hX : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase s.site.contains_terminal
      s.space.1)
    {Z : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {i : Z ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (V : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1)
    (hV : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left))
    [hiV : _root_.AlgebraicGeometry.IsClosedImmersion (s.fibreClosedImmersion hi V.1.left V.1.hom)]
    [hπV : QuasiCompact (relativeProj (s.shrink.pointAlgebra V.1.left V.1.hom)).toBase] {d : ℕ}
    (ℱ' : ((s.shrink.pointAlgebra V.1.left V.1.hom).piece (d : ℤ)).Submodule)
    (hℱ'q : ℱ'.toSheafOfModules.IsQuasicoherent)
    (hℱ'f : SheafOfModules.IsFiniteType.{u, u, u} ℱ'.toSheafOfModules)
    (hℱ'K : ℱ' ≤ (twistKerGradedIdeal (s.shrink.pointAlgebra V.1.left V.1.hom)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
      (s.fibreClosedImmersion hi V.1.left V.1.hom)).piece (d : ℤ)) :
    ∃ (ℱ : (s.algebra.piece (d : ℤ)).Submodule) (_ : ℱ.toSheafOfModules.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteType ℱ.toSheafOfModules ∧
        ℱ' ≤ s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ ∧
          s.pointZariskiImageSubmodule (T := V.1.left) V.1.hom ℱ ≤
            (twistKerGradedIdeal (s.shrink.pointAlgebra V.1.left V.1.hom)
              (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
              (s.fibreClosedImmersion hi V.1.left V.1.hom)).piece (d : ℤ) := by
  classical
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left) := hV
  have := hℱ'q
  have := hℱ'f
  obtain ⟨gens, hgens, hgensle⟩ :=
    s.exists_finset_le_pointZariskiImageSubmodule V hV ℱ' hℱ'q hℱ'f
  have hρ := bijective_chartOpenReading_top s.shrink.algebra V hV (d : ℤ)
    (s.shrink.isQuasicoherent (d : ℤ))
  obtain ⟨a, hay⟩ : ∃ a : gens → (s.shrink.algebra.piece (d : ℤ)).val.obj (op V),
      ∀ j, chartOpenReading s.shrink.algebra V ⊤ (d : ℤ) (a j) = j.1 :=
    ⟨fun j => Function.surjInv hρ.2 j.1, fun j => Function.surjInv_eq hρ.2 j.1⟩
  have ha : ∀ j, a j ∈ (s.chartIdeal hi hπ d).obj (op V) := fun j =>
    s.isChartEquation_of_twistEquationSection_eq_zero hi (a j)
      ((congrArg (twistEquationSection (s.shrink.pointAlgebra V.1.left V.1.hom)
        (s.fibreClosedImmersion hi V.1.left V.1.hom) d) (hay j)).trans
        ((twistEquationSection_eq_zero_iff _ _ d j.1).2
          (PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp hℱ'K)
            (op ⊤) (hgens j.1 j.2))))
  obtain ⟨N, hNq, hNf, hNmem⟩ := exists_isFiniteType_submodule_mem_of_qcqs (B := s.site)
    (S := s.base) (hS := s.containsBase)
    s.site.contains_terminal s.space hX hXqs (s.chartIdeal hi hπ d).toSheafOfModules
    (s.isQuasicoherentOnSite_chartIdeal hi hπ d) (ι := gens) (fun _ => V) (fun _ => hV)
    (fun j => ⟨a j, ha j⟩)
  obtain ⟨φ0, hφ0app, hφ0⟩ : ∃ φ0 : N.toSheafOfModules ⟶ s.algebra.piece (d : ℤ),
      (∀ m : N.toSheafOfModules.val.obj (op V), (s.smallAlgebraPieceIso (d : ℤ)).inv.val.app
        (op V) (φ0.val.app (op V) m) = m.1.1) ∧ Mono φ0 := by
    let ιI : ((s.chartIdeal hi hπ d).toSheafOfModules :
        Modules.{u, u} s.site s.base s.containsBase s.space.1 s.space.2) ⟶
        s.smallAlgebra.piece (d : ℤ) := (s.chartIdeal hi hπ d).ι
    exact ⟨N.ι ≫ ιI ≫ (s.smallAlgebraPieceIso (d : ℤ)).hom, fun m =>
      congrArg (fun χ : s.smallAlgebra.piece (d : ℤ) ⟶ s.smallAlgebra.piece (d : ℤ) =>
        χ.val.app (op V) m.1.1) (s.smallAlgebraPieceIso (d : ℤ)).hom_inv_id,
      @mono_comp _ _ _ _ _ N.ι (SheafOfModules.Submodule.mono_ι_via_forget N) _
        (@mono_comp _ _ _ _ _ ιI
          (SheafOfModules.Submodule.mono_ι_via_forget (s.chartIdeal hi hπ d)) _
          (IsIso.mono_of_iso (s.smallAlgebraPieceIso (d : ℤ)).hom))⟩
  obtain ⟨hℱq, hℱf⟩ := @isQuasicoherentOnSite_and_isFiniteType_monoRangeSubmodule s.site s.base
    s.containsBase s.space _ _ φ0 hφ0 hNq hNf
  obtain ⟨ℱ, hℱq, hℱf, hmem⟩ : ∃ ℱ : (s.algebra.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherentOnSite ∧ SheafOfModules.IsFiniteType ℱ.toSheafOfModules ∧
        ∀ b : (s.algebra.piece (d : ℤ)).val.obj (op V),
          b ∈ ℱ.obj (op V) ↔ ∃ m, φ0.val.app (op V) m = b := ⟨_, hℱq, hℱf, fun _ => Iff.rfl⟩
  refine ⟨ℱ, hℱq, hℱf, hgensle ℱ fun w hw => ?_,
    s.pointZariskiImageSubmodule_le_twistKer V hi hV ℱ hℱq fun b hb => ?_⟩
  · exact ⟨φ0.val.app (op V) ⟨⟨a ⟨w, hw⟩, ha ⟨w, hw⟩⟩, hNmem ⟨w, hw⟩⟩, (hmem _).2 ⟨_, rfl⟩,
      (congrArg (chartOpenReading s.shrink.algebra V ⊤ (d : ℤ)) (hφ0app _)).trans (hay ⟨w, hw⟩)⟩
  · obtain ⟨m, rfl⟩ := (hmem b).1 hb
    exact (congrArg (s.IsChartEquation hi d V) (hφ0app m)).mpr m.1.2

end AlgebraicGeometry.Space.RelativeProjSituation

end

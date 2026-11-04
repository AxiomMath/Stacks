module

public import StacksFrontier.Algebra.Homology.RightExactHomologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankFitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorAmplitudeKFlatModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact

/-!
# Base change of the bottom cohomology of a K-flat complex

For a morphism `g : Y ⟶ Z` of algebraic spaces and a complex `N` of `𝒪_Z`-modules, the right exact
functor `g^*` comes with the comparison `g^* H^a(N) ⟶ H^a(g^* N)`
(`CategoryTheory.Functor.homologyComparisonRightExactHomologyComparison`). For `N` a K-flat
complex with flat terms, this comparison being an isomorphism only depends on the image of `N`
in `D(𝒪_Z)` among such complexes, and it is an isomorphism for a bottom model whose matrix has a
free kernel splitting.

## Main results

* `AlgebraicGeometry.Space.isIso_Q_map_pb`: degreewise pullback preserves quasi-isomorphisms
  between K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.isIso_homologyComparison_iff_of_iso`: for K-flat complexes with
  flat terms which are isomorphic in the derived category, the comparisons are isomorphisms
  together.
* `AlgebraicGeometry.Space.BottomModel.isIso_homologyComparison`: the comparison is an
  isomorphism for a bottom model whose matrix has a free kernel splitting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of modules along a morphism of algebraic spaces is right exact, being a left
adjoint. -/
instance preservesFiniteColimits_pb {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    PreservesFiniteColimits (pb g) := by
  have : (pb g).IsLeftAdjoint := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  exact PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} (pb g)

/-- Pullback along an étale chart is exact. -/
theorem preservesFiniteLimits_pb_chartToSpace (Y : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Y.1) : PreservesFiniteLimits (pb (chartToSpace B S hS Y V)) := by
  let a := chartToSpace B S hS Y V
  let ha := isEtale_chartToSpace B S hS Y V
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  exact preservesFiniteLimits_of_natIso (F := etaleModulePullback.{u, u} B S hS a ha)
    (modulePullbackIsoEtaleModulePullback B S hS a ha).symm

variable {X Y : AlgebraicSpaces B S hS}


/-- The comparison along equal morphisms. -/
theorem isIso_homologyComparison_congr {Z : AlgebraicSpaces B S hS} {f f' : Y ⟶ Z} (h : f = f')
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ) (a : ℤ)
    [(pb f).Additive] [PreservesFiniteColimits (pb f)] [(pb f').Additive]
    [PreservesFiniteColimits (pb f')] :
    IsIso ((pb f).homologyComparisonRightExactHomologyComparison N a) ↔
      IsIso ((pb f').homologyComparisonRightExactHomologyComparison N a) := by
  subst h
  rfl

/-- **Degreewise pullback preserves quasi-isomorphisms between K-flat complexes with flat
terms**: both compute the derived pullback. -/
theorem isIso_Q_map_pb (f : Y ⟶ X)
    {K K' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (u : K ⟶ K')
    (hK : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : smallEtaleModuleKFlat B S hS X
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    [IsIso (DerivedCategory.Q.map u)] :
    IsIso (DerivedCategory.Q.map (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).map u)) := by
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ)
  let c := smallEtaleDerivedModulePullbackComparison B S hS f
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _ hK
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _ hK'
  have : IsIso (DerivedCategory.Qh.map (q.map u)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) u).2 inferInstance
  have h₁ : IsIso ((smallEtaleModulePullbackOnHomotopy B S hS f).map (q.map u)) := by
    rw [← isIso_comp_left_iff (c.app (q.obj K)), ← c.naturality (q.map u)]
    show IsIso ((smallEtaleDerivedModulePullback B S hS f).map
      (DerivedCategory.Qh.map (q.map u)) ≫ c.app (q.obj K'))
    infer_instance
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS Y)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  have h₂ : IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map u)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).1 h₁
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (F := F)
    (G := G) (pullbackModulesIsoModulePullback B S hS f) (ComplexShape.up ℤ))
      DerivedCategory.Q) u).1 h₂

/-- The comparison `f^* H^a ⟶ H^a f^*` for a quasi-isomorphism `u` between K-flat complexes with
flat terms: one is an isomorphism exactly when the other is. -/
theorem isIso_homologyComparison_iff_of_isIso_Q_map (f : Y ⟶ X)
    {K K' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (u : K ⟶ K')
    (hK : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : smallEtaleModuleKFlat B S hS X
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    [IsIso (DerivedCategory.Q.map u)] (a : ℤ) :
    IsIso ((pb f).homologyComparisonRightExactHomologyComparison K a) ↔
      IsIso ((pb f).homologyComparisonRightExactHomologyComparison K' a) := by
  have := isIso_Q_map_pb f u hK hK'
  have : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ u).1 inferInstance
  have : QuasiIso (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).map u) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 inferInstance
  have w := (pb f).homologyComparison_naturality_rightExactHomologyComparison a u
  rw [← isIso_comp_left_iff ((pb f).map (HomologicalComplex.homologyMap u a)), w,
    isIso_comp_right_iff]

/-- **The comparison only depends on the derived category.** For K-flat complexes with flat terms
`N` and `P` isomorphic in `D(𝒪_X)`, the comparisons `f^* H^a ⟶ H^a f^*` are isomorphisms
together: both are compared with a common K-flat resolution. -/
theorem isIso_homologyComparison_iff_of_iso (f : Y ⟶ X)
    {N P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (hN : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (hP : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (φ : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj P) (a : ℤ) :
    IsIso ((pb f).homologyComparisonRightExactHomologyComparison N a) ↔
      IsIso ((pb f).homologyComparisonRightExactHomologyComparison P a) := by
  obtain ⟨X', s, hs, g, hφ⟩ := DerivedCategory.right_fac φ.hom
  have hg : IsIso (DerivedCategory.Q.map g) := by
    rw [show DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ φ.hom by
      rw [hφ, IsIso.hom_inv_id_assoc]]
    infer_instance
  obtain ⟨R₀, hR₀, t₀, ht₀⟩ := smallEtaleModuleKFlat_hasResolutions B S hS X
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X')
  obtain ⟨R, rfl⟩ := HomotopyCategory.quotient_obj_surjective R₀
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective t₀
  have : IsIso (DerivedCategory.Q.map t) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso, ← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact ht₀
  have : IsIso (DerivedCategory.Q.map (t ≫ s)) := by rw [Functor.map_comp]; infer_instance
  have : IsIso (DerivedCategory.Q.map (t ≫ g)) := by rw [Functor.map_comp]; infer_instance
  exact (isIso_homologyComparison_iff_of_isIso_Q_map f (t ≫ s) hR₀ hN a).symm.trans
    (isIso_homologyComparison_iff_of_isIso_Q_map f (t ≫ g) hR₀ hP a)

namespace BottomModel

variable {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {R : Type u} [CommRing R] {ψ : R →+* End (ringedToposUnit X)} {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) R}

/-- **For a bottom model whose matrix has a free kernel splitting, `f^*` commutes with `H^a`.**
The kernel of the differential in degree `a` is split, so every additive functor preserves
it. -/
theorem isIso_homologyComparison (M : BottomModel K a ψ A) {r : ℕ}
    (h : A.HasFreeKernelSplittingKernelRankStratum r) (f : Y ⟶ X) :
    IsIso ((pb f).homologyComparisonRightExactHomologyComparison M.P a) := by
  obtain ⟨U, V, W, h₁, h₂, h₃⟩ := h
  let O := ringedToposUnit X
  let u : freeObjMatrixKernelSplitting O r ⟶ M.P.X a :=
    matrixHomMatrixKernelSplitting O ψ U ≫ M.e₀.inv
  let v : M.P.X a ⟶ freeObjMatrixKernelSplitting O r :=
    M.e₀.hom ≫ matrixHomMatrixKernelSplitting O ψ V
  let w : M.P.X (a + 1) ⟶ M.P.X a := M.e₁.hom ≫ matrixHomMatrixKernelSplitting O ψ W ≫ M.e₀.inv
  have e₁ : u ≫ v = 𝟙 _ := by
    simp only [u, v, Category.assoc, Iso.inv_hom_id_assoc, ← matrixHom_mul_matrixKernelSplitting,
      h₁, matrixHom_one_matrixKernelSplitting]
  have e₂ : u ≫ M.P.d a (a + 1) = 0 := by
    rw [M.d_eq]
    simp only [u, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← matrixHom_mul_matrixKernelSplitting, h₂,
      matrixHom_zero_matrixKernelSplitting, zero_comp]
  have e₃ : M.P.d a (a + 1) ≫ w + v ≫ u = 𝟙 _ := by
    rw [M.d_eq]
    simp only [u, v, w, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (matrixHomMatrixKernelSplitting O ψ A),
      ← matrixHom_mul_matrixKernelSplitting,
      ← Category.assoc (matrixHomMatrixKernelSplitting O ψ V),
      ← matrixHom_mul_matrixKernelSplitting,
      ← Preadditive.comp_add, ← Preadditive.add_comp, ← matrixHom_add_matrixKernelSplitting, h₃,
      matrixHom_one_matrixKernelSplitting, Category.id_comp, Iso.hom_inv_id]
  have :=
    (pb f).isIso_cyclesComparison_of_splitting_rightExactHomologyComparison M.P a u v w e₁ e₂ e₃
  exact (pb f).isIso_homologyComparison_of_isIso_cyclesComparison_rightExactHomologyComparison M.P a

/-- The complex of a bottom model is K-flat with flat terms. -/
theorem smallEtaleModuleKFlat_P (M : BottomModel K a ψ A) :
    smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M.P) :=
  have := M.isStrictlyLE
  smallEtaleModuleKFlat_of_isStrictlyLE B S hS X M.P M.b
    (fun j => isFlat_of_isRetractOfFiniteFree B S hS _ (M.retract j))

/-- A bottom model of `K` is a bottom model of anything isomorphic to `K`. -/
def ofIso (M : BottomModel K a ψ A)
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (e : K' ≅ K) : BottomModel K' a ψ A where
  P := M.P
  retract := M.retract
  b := M.b
  isStrictlyLE := M.isStrictlyLE
  isStrictlyGE := M.isStrictlyGE
  e₀ := M.e₀
  e₁ := M.e₁
  hd := M.hd
  iso := e ≪≫ M.iso

end BottomModel

/-- **The comparison on a chart with a split bottom model.** Let `φ` be a morphism from the space
represented by `U` along which pullback is exact, and `N` a K-flat complex with flat terms on `Z`
such that `Lφ^*N` has a bottom model with a split matrix. Then `(t ∘ φ)^*` commutes with `H^a` on
`N`, for every `t` to the space represented by `U`. -/
theorem isIso_homologyComparison_of_bottomModel {Z : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (φ : representedAlgebraicSpace B S hS U ⟶ Z)
    [PreservesFiniteLimits (pb φ)]
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hN : smallEtaleModuleKFlat B S hS Z ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    {a : ℤ} {m n r : ℕ} {A : Matrix (Fin m) (Fin n) (repRing U)}
    (M : BottomModel (Y := representedAlgebraicSpace B S hS U)
      ((smallEtaleDerivedModulePullback B S hS φ).obj (DerivedCategory.Q.obj N)) a (repRho U) A)
    (hA : A.HasFreeKernelSplittingKernelRankStratum r) {Y' : AlgebraicSpaces B S hS}
    (t : Y' ⟶ representedAlgebraicSpace B S hS U) :
    haveI : (pb (t ≫ φ)).Additive := modulePullback_additive _
    haveI := preservesFiniteColimits_pb (t ≫ φ)
    IsIso ((pb (t ≫ φ)).homologyComparisonRightExactHomologyComparison N a) := by
  have : ∀ {W V : AlgebraicSpaces B S hS} (g : W ⟶ V), (pb g).Additive :=
    fun g => modulePullback_additive g
  have := @preservesFiniteColimits_pb B S hS
  have : IsIso ((pb φ).homologyComparisonRightExactHomologyComparison N a) :=
    (pb φ).isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison N a
  have hN' := smallEtaleModuleKFlat_pb φ N hN
  have : IsIso ((pb t).homologyComparisonRightExactHomologyComparison
      (((pb φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) a) :=
    (isIso_homologyComparison_iff_of_iso t hN' M.smallEtaleModuleKFlat_P
      ((smallEtaleDerivedModulePullbackObjQIsoOfKFlat φ N hN).symm ≪≫ M.iso) a).2
      (M.isIso_homologyComparison hA _)
  exact Functor.isIso_homologyComparison_of_comp_rightExactHomologyComparison (pb φ) (pb t)
    (pb (t ≫ φ)) (modulePullbackCompIso B S hS t φ) N a

end AlgebraicGeometry.Space

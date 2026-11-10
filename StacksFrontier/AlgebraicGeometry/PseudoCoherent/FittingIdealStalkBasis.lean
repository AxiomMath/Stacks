module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealCochainModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealFreeModelBasis

/-!
# The stalk of a finite free model is the base change of its matrices

`AlgebraicGeometry.DerivedFreeModel K U` records a bounded-above finite free model, over the open
`U`, of a complex `K` of `𝒪_X`-modules, and `AlgebraicGeometry.DerivedFreeModel.matrix` reads the
matrix of its differential in the chosen bases of its sections over `U`. The proof of [Stacks, Tag
0ESP] is carried out over a local ring, and the local rings it uses are the local rings `𝒪_{X,x}`
of the points of `U`. This file supplies the passage: at a point `x` of `U` the stalk of the
modelling complex is the cochain complex of `𝒪_{X,x}`-modules presented by the *entrywise germs* of
the matrices of the model, which is `Stacks.FittingComplex.FreeData.map` along the germ map
`Γ(X, U) → 𝒪_{X,x}`.

The content is the comparison of the chosen bases with the stalk. The chosen basis of a model is
arbitrary data; what makes its germs a basis of the stalk is that for every `V ≤ U` the
*restrictions* of its vectors are again a basis of the sections over `V`
(`AlgebraicGeometry.DerivedFreeModel.exists_basis_restrict`, which is the `basis` field of
`AlgebraicGeometry.DerivedFreeModel.exists_restrict` isolated). Given such a family, the map
sending a family of scalars to the corresponding combination of germs is bijective — surjective
because every element of a stalk is the germ of a section over some open, which may be shrunk
inside `U` and expanded in the basis there; injective because a relation among the germs is
realized over a single open, where the basis is linearly independent.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.stalkGerm`: the germ of a section, as an additive map into the
  stalk module `Stacks.Duality.modulesStalkFunctor x`, whose scalars are the `CommRingCat`-valued
  stalk `𝒪_{X,x}`.
* `AlgebraicGeometry.DerivedFreeModel.stalkFreeData`: the numerical data of a finite free model
  base changed along the germ map at a point of `U`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_stalkBasis`: a family of bases of the sections over the
  opens inside `U`, each the restriction of a fixed basis over `U`, makes the stalk at a point of
  `U` free on the germs of that basis, with the germs of the coordinates as coordinates.
* `AlgebraicGeometry.DerivedFreeModel.exists_stalkBasis`: that basis for one degree of a finite
  free model.
* `AlgebraicGeometry.DerivedFreeModel.matrix_mul_matrix`: the matrices of two consecutive
  differentials compose to zero, so the base changed matrices present a cochain complex
  (`AlgebraicGeometry.DerivedFreeModel.stalkFreeData_dd`).
* `AlgebraicGeometry.DerivedFreeModel.stalkFreeData_fittingIdeal`: the Fitting ideals of the base
  changed data are the base changes of the ideals of minors of the model.
* `AlgebraicGeometry.DerivedFreeModel.nonempty_stalkCochain_iso`: **the comparison** — the
  degreewise stalk of the modelling complex is the cochain complex presented by the base changed
  matrices.

## Implementation notes

The stalk functor used is `Stacks.Duality.modulesStalkFunctor`, which takes values in modules over
the `CommRingCat`-valued stalk `X.presheaf.stalk x`; this is what the Fitting ideals need, the
`RingCat`-valued stalk of `AlgebraicGeometry.SheafOfModules.stalkFunctor` carrying no
commutativity. Its scalar action is read through
`Stacks.Duality.schemeStalkModuleFunctor_germ_smul`, which is the only property of that module
structure used here, so no comparison of the two stalk rings is needed.
`AlgebraicGeometry.Scheme.Modules.stalkGerm` is `Stacks.SheafOfModules.germAddHom` with its target
spelled as that module, which is the spelling in which instance search finds the action.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}}

/-- The germ at `x` of a section over `V` of an `𝒪_X`-module, as an additive map into the stalk
module `Stacks.Duality.modulesStalkFunctor x`. This is
`Stacks.SheafOfModules.germAddHom` with its target spelled as that module, which is the spelling
in which the scalar action of `𝒪_{X,x}` is found by instance search. -/
def Scheme.Modules.stalkGerm (N : X.Modules) (x : X) (V : X.Opens) (hx : x ∈ V) :
    Γ(N, V) →+ ((Stacks.Duality.modulesStalkFunctor x).obj N) :=
  Stacks.SheafOfModules.germAddHom (R := X.presheaf) N.val V hx

/-- The germ at `x` of a scalar multiple of a section, in the stalk module of
`Stacks.Duality.modulesStalkFunctor`. -/
theorem Scheme.Modules.germAddHom_smul_modulesStalk (N : X.Modules) (x : X) (V : X.Opens)
    (hx : x ∈ V) (a : Γ(X, V)) (s : Γ(N, V)) :
    Scheme.Modules.stalkGerm N x V hx (a • s) =
      X.presheaf.germ V x hx a • Scheme.Modules.stalkGerm N x V hx s :=
  Stacks.Duality.schemeStalkModuleFunctor_germ_smul x N V hx a s

/-- The germ of a section over `V` is the germ over a larger open of any section restricting to
it. -/
theorem Scheme.Modules.stalkGerm_map (N : X.Modules) (x : X) {V W : X.Opens} (h : V ≤ W)
    (hx : x ∈ V) (s : Γ(N, W)) :
    Scheme.Modules.stalkGerm N x V hx (N.presheaf.map (homOfLE h).op s) =
      Scheme.Modules.stalkGerm N x W (h hx) s :=
  Stacks.SheafOfModules.germAddHom_resAddHom (R := X.presheaf) N.val h hx s

/-- The stalk of a morphism of `𝒪_X`-modules sends the germ of a section to the germ of its
image. -/
theorem Scheme.Modules.map_stalkGerm {N P : X.Modules} (f : N ⟶ P) (x : X) (V : X.Opens)
    (hx : x ∈ V) (s : Γ(N, V)) :
    ((Stacks.Duality.modulesStalkFunctor x).map f).hom
        (Scheme.Modules.stalkGerm N x V hx s) =
      Scheme.Modules.stalkGerm P x V hx ((f.val.app (op V)) s) :=
  AlgebraicGeometry.SheafOfModules.stalkMap_germ X.ringCatSheaf x f V hx s

/-- **A family of bases of the sections over the opens inside `U`, each the restriction of a
fixed basis over `U`, makes the stalk at a point of `U` free on the germs of that basis.**

The coordinates in the resulting basis of the germ of a section over `U` are the germs of its
coordinates. -/
theorem Scheme.Modules.exists_stalkBasis (N : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U)
    {n : ℕ} (c : Module.Basis (Fin n) Γ(X, U) Γ(N, U))
    (hres : ∀ (V : X.Opens) (hVU : V ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, V) Γ(N, V),
      ∀ k, b k = N.presheaf.map (homOfLE hVU).op (c k)) :
    ∃ β : Module.Basis (Fin n) ↑(X.presheaf.stalk x)
        ↑((Stacks.Duality.modulesStalkFunctor x).obj N),
      (∀ k, β k = Scheme.Modules.stalkGerm N x U hx (c k)) ∧
      ∀ (s : Γ(N, U)) (k : Fin n),
        β.repr (Scheme.Modules.stalkGerm N x U hx s) k =
          X.presheaf.germ U x hx (c.repr s k) := by
  classical
  choose b hb using hres
  set e : Fin n → ↑((Stacks.Duality.modulesStalkFunctor x).obj N) :=
    fun k => Scheme.Modules.stalkGerm N x U hx (c k) with he
  set θ : (Fin n → ↑(X.presheaf.stalk x)) →ₗ[↑(X.presheaf.stalk x)]
      ↑((Stacks.Duality.modulesStalkFunctor x).obj N) :=
    ∑ k : Fin n, (LinearMap.toSpanSingleton ↑(X.presheaf.stalk x) _ (e k)).comp
      (LinearMap.proj k) with hθdef
  have hθ : ∀ v : Fin n → ↑(X.presheaf.stalk x), θ v = ∑ k : Fin n, v k • e k := by
    intro v
    rw [hθdef, LinearMap.sum_apply]
    rfl
  have hgerm : ∀ (V : X.Opens) (hVU : V ≤ U) (hxV : x ∈ V) (k : Fin n),
      Scheme.Modules.stalkGerm N x V hxV (b V hVU k) = e k := by
    intro V hVU hxV k
    rw [hb V hVU k]
    exact Scheme.Modules.stalkGerm_map N x hVU hxV (c k)
  have key : ∀ (V : X.Opens) (hxV : x ∈ V) (b' : Module.Basis (Fin n) Γ(X, V) Γ(N, V)),
      (∀ k, Scheme.Modules.stalkGerm N x V hxV (b' k) = e k) → ∀ s : Γ(N, V),
      θ (fun k => X.presheaf.germ V x hxV (b'.repr s k)) =
        Scheme.Modules.stalkGerm N x V hxV s := by
    intro V hxV b' hb' s
    rw [hθ]
    conv_rhs => rw [← b'.sum_repr s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hb' k]
    exact (Scheme.Modules.germAddHom_smul_modulesStalk N x V hxV _ _).symm
  have keyU := key U hx c fun _ => rfl
  have hsurj : Function.Surjective θ := by
    intro m
    obtain ⟨W, hxW, s, hs⟩ := TopCat.Presheaf.exists_germ_eq N.val.presheaf m
    refine ⟨fun k => X.presheaf.germ (W ⊓ U) x ⟨hxW, hx⟩
      ((b (W ⊓ U) inf_le_right).repr
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s) k), ?_⟩
    rw [key (W ⊓ U) ⟨hxW, hx⟩ (b (W ⊓ U) inf_le_right) (hgerm _ inf_le_right _) _]
    exact (Scheme.Modules.stalkGerm_map N x (inf_le_left : W ⊓ U ≤ W) ⟨hxW, hx⟩ s).trans hs
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    choose W hW a ha using fun k : Fin n => TopCat.Presheaf.exists_germ_eq X.presheaf (v k)
    have hmem : x ∈ ((⨅ k, W k) ⊓ U : X.Opens) := by
      refine ⟨?_, hx⟩
      simp only [Opens.coe_iInf, Set.mem_iInter]
      exact hW
    set V : X.Opens := (⨅ k, W k) ⊓ U with hVdef
    have hVU : V ≤ U := inf_le_right
    set cV : Fin n → Γ(X, V) := fun k =>
      X.presheaf.map (homOfLE (le_trans inf_le_left (iInf_le W k))).op (a k) with hcV
    have hcg : ∀ k, X.presheaf.germ V x hmem (cV k) = v k := fun k =>
      (X.presheaf.germ_res_apply _ x hmem (a k)).trans (ha k)
    have hs0 : Scheme.Modules.stalkGerm N x V hmem (∑ k, cV k • (b V hVU k)) = 0 := by
      rw [map_sum, ← hv, hθ]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.germAddHom_smul_modulesStalk N x V hmem, hgerm V hVU hmem k, hcg k]
    obtain ⟨W', hxW', iW'V, iW'V', hW'⟩ := TopCat.Presheaf.germ_eq N.val.presheaf x hmem hmem
      (∑ k, cV k • (b V hVU k)) 0 (by rw [map_zero]; exact hs0)
    have hle : W' ≤ V := leOfHom iW'V
    have hres0 : (N.val.presheaf.map (homOfLE hle).op) (∑ k, cV k • (b V hVU k)) = 0 := by
      rw [show (homOfLE hle : W' ⟶ V) = iW'V from Subsingleton.elim _ _, hW',
        show (N.val.presheaf.map iW'V'.op) 0 = 0 from map_zero _]
    have hzero : ∑ k, (X.presheaf.map (homOfLE hle).op) (cV k) •
        (b W' (hle.trans hVU) k) = 0 := by
      refine Eq.trans (Eq.symm (Eq.trans (map_sum (Scheme.Modules.resAddHom N hle) _ _)
        (Finset.sum_congr rfl fun k _ => ?_))) hres0
      refine (Scheme.Modules.resAddHom_smul N hle (cV k) (b V hVU k)).trans ?_
      refine congrArg (fun t => (X.presheaf.map (homOfLE hle).op) (cV k) • t) ?_
      rw [Scheme.Modules.resAddHom_apply, hb V hVU k, hb W' (hle.trans hVU) k,
        ← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
      rfl
    have hcoef := fun k => Fintype.linearIndependent_iff.1 (b W' (hle.trans hVU)).linearIndependent
      (fun k => (X.presheaf.map (homOfLE hle).op) (cV k)) hzero k
    funext k
    rw [← hcg k, ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) x hxW' (cV k),
      show (X.presheaf.map (homOfLE hle).op) (cV k) = 0 from hcoef k, map_zero]
    rfl
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩).symm, fun k => ?_,
    fun s k => ?_⟩
  · rw [Module.Basis.coe_ofEquivFun]
    change (LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩) (Pi.single k 1) = _
    rw [show (LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩) (Pi.single k 1) = θ (Pi.single k 1) from rfl,
      hθ, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]), Pi.single_eq_same, one_smul]
  · rw [Module.Basis.ofEquivFun_repr_apply, ← keyU s]
    exact congrFun ((LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩).symm_apply_apply _) k


namespace DerivedFreeModel

variable {K : CochainComplex X.Modules ℤ} {U : X.Opens}

/-- **A basis of the sections of one degree of a finite free model over a smaller open whose
vectors are the restrictions of the chosen ones.** This is the `basis` field of
`AlgebraicGeometry.DerivedFreeModel.exists_restrict`, isolated: the restriction of an arbitrary
basis is a basis because the trivialization recorded by `isFree` provides a pair of bases matched
by the restriction maps. -/
theorem exists_basis_restrict (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U) (i : ℤ) :
    ∃ b : Module.Basis (Fin (M.rank i)) Γ(X, V) Γ(M.model.X i, V),
      ∀ k, b k = (M.model.X i).presheaf.map (homOfLE hVU).op (M.basis i k) := by
  obtain ⟨g, g', hgg⟩ := M.exists_basis_pair hVU i
  exact ⟨Stacks.basisOfSemilinearImage (X.presheaf.map (homOfLE hVU).op).hom g g' (M.basis i),
    fun k => Stacks.basisOfSemilinearImage_apply _ (Scheme.Modules.resAddHom (M.model.X i) hVU)
      (Scheme.Modules.resAddHom_smul (M.model.X i) hVU) g g' hgg (M.basis i) k⟩

/-- **The stalk at a point of `U` of one degree of a finite free model is free on the germs of
the chosen basis**, and the coordinates there of the germ of a section are the germs of its
coordinates. -/
theorem exists_stalkBasis (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) (i : ℤ) :
    ∃ β : Module.Basis (Fin (M.rank i)) ↑(X.presheaf.stalk x)
        ↑((Stacks.Duality.modulesStalkFunctor x).obj (M.model.X i)),
      (∀ k, β k = Scheme.Modules.stalkGerm (M.model.X i) x U hx (M.basis i k)) ∧
      ∀ (s : Γ(M.model.X i, U)) (k : Fin (M.rank i)),
        β.repr (Scheme.Modules.stalkGerm (M.model.X i) x U hx s) k =
          X.presheaf.germ U x hx ((M.basis i).repr s k) :=
  Scheme.Modules.exists_stalkBasis _ hx (M.basis i) fun _ hVU => M.exists_basis_restrict hVU i

/-- The matrices of two consecutive differentials of a finite free model compose to zero. -/
theorem matrix_mul_matrix (M : DerivedFreeModel K U) (i : ℤ) :
    M.matrix (i + 1) * M.matrix i = 0 := by
  have h0 : M.model.d i (i + 1) ≫ M.model.d (i + 1) (i + 1 + 1) = 0 :=
    M.model.d_comp_d i (i + 1) (i + 1 + 1)
  have hcomp : ((M.model.d (i + 1) (i + 1 + 1)).val.app (op U)).hom ∘ₗ
      ((M.model.d i (i + 1)).val.app (op U)).hom = 0 :=
    congrArg (fun φ : M.model.X i ⟶ M.model.X (i + 1 + 1) => (φ.val.app (op U)).hom) h0
  calc M.matrix (i + 1) * M.matrix i
      = LinearMap.toMatrix (M.basis i) (M.basis (i + 1 + 1))
          (((M.model.d (i + 1) (i + 1 + 1)).val.app (op U)).hom ∘ₗ
            ((M.model.d i (i + 1)).val.app (op U)).hom) :=
        (LinearMap.toMatrix_comp (M.basis i) (M.basis (i + 1)) (M.basis (i + 1 + 1)) _ _).symm
    _ = 0 :=
        (congrArg (fun f => LinearMap.toMatrix (M.basis i) (M.basis (i + 1 + 1)) f)
          hcomp).trans (map_zero _)

/-- **The numerical data of a finite free model, base changed to the local ring at a point of
`U`** along the germ map `Γ(X, U) → 𝒪_{X,x}`: the ranks are unchanged and each matrix is replaced
by its entrywise germ. -/
noncomputable def stalkFreeData (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) :
    Stacks.FittingComplex.FreeData ↑(X.presheaf.stalk x) :=
  M.toFreeData.map (X.presheaf.germ U x hx).hom

/-- The matrix in degree `i` of the base changed data is the entrywise germ of the matrix of the
model in degree `i`. -/
theorem stalkFreeData_d (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) (i : ℤ) :
    (M.stalkFreeData hx).d i = (M.matrix i).map (X.presheaf.germ U x hx).hom := rfl

/-- The ranks of the base changed data are the ranks of the model. -/
theorem stalkFreeData_rank (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) :
    (M.stalkFreeData hx).rank = M.rank := rfl

/-- The base changed matrices still compose to zero, so they present a cochain complex. -/
theorem stalkFreeData_dd (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) (i : ℤ) :
    (M.stalkFreeData hx).d (i + 1) * (M.stalkFreeData hx).d i = 0 := by
  have h : (M.matrix (i + 1)).map (X.presheaf.germ U x hx).hom *
      (M.matrix i).map (X.presheaf.germ U x hx).hom = 0 := by
    rw [← Matrix.map_mul, M.matrix_mul_matrix i, Matrix.map_zero _ (map_zero _)]
  exact h

/-- The `(p, k)`-th Fitting ideal of the base changed data is the base change of the `(p, k)`-th
ideal of minors of the model. -/
theorem stalkFreeData_fittingIdeal (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) (p k : ℤ) :
    (M.stalkFreeData hx).fittingIdeal p k =
      Ideal.map (X.presheaf.germ U x hx).hom (M.fittingIdeal p k) :=
  (M.toFreeData.map_fittingIdeal (X.presheaf.germ U x hx).hom p k).symm


/-- **The degreewise stalk at a point of `U` of the modelling complex of a finite free model is
the cochain complex presented by the base changed matrices.** -/
theorem nonempty_stalkCochain_iso (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) :
    Nonempty (((Stacks.Duality.modulesStalkFunctor x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.model ≅
      (M.stalkFreeData hx).toCochain (M.stalkFreeData_dd hx)) := by
  classical
  choose β hβ hβrepr using fun i => M.exists_stalkBasis hx i
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun i => LinearEquiv.toModuleIso (β i).equivFun) ?_⟩
  intro i j hij
  obtain rfl : j = i + 1 := hij.symm
  rw [Stacks.FittingComplex.FreeData.toCochain_d]
  refine ModuleCat.hom_ext ((β i).ext fun k => ?_)
  have h1 : (β i).equivFun (β i k) = Pi.single k 1 := by
    rw [Module.Basis.equivFun_apply, (β i).repr_self]
    exact Finsupp.single_eq_pi_single k 1
  have h2 : ((Stacks.Duality.modulesStalkFunctor x).map (M.model.d i (i + 1))).hom (β i k) =
      Scheme.Modules.stalkGerm (M.model.X (i + 1)) x U hx
        ((M.model.d i (i + 1)).val.app (op U) (M.basis i k)) := by
    rw [hβ i k]
    exact Scheme.Modules.map_stalkGerm _ x U hx _
  change Matrix.toLin' ((M.stalkFreeData hx).d i) ((β i).equivFun (β i k)) =
    (β (i + 1)).equivFun
      (((Stacks.Duality.modulesStalkFunctor x).map (M.model.d i (i + 1))).hom (β i k))
  have h4 : Matrix.toLin' ((M.stalkFreeData hx).d i) ((β i).equivFun (β i k)) =
      ((M.stalkFreeData hx).d i).col k :=
    ((Matrix.toLin'_apply _ _).trans (congrArg _ h1)).trans
      (Matrix.mulVec_single_one ((M.stalkFreeData hx).d i) k)
  rw [h4, h2]
  funext a
  change X.presheaf.germ U x hx (M.matrix i a k) =
    (β (i + 1)).equivFun (Scheme.Modules.stalkGerm (M.model.X (i + 1)) x U hx
      ((M.model.d i (i + 1)).val.app (op U) (M.basis i k))) a
  rw [Module.Basis.equivFun_apply,
    hβrepr (i + 1) ((M.model.d i (i + 1)).val.app (op U) (M.basis i k)) a]
  exact congrArg (X.presheaf.germ U x hx)
    (LinearMap.toMatrix_apply (M.basis i) (M.basis (i + 1)) _ a k)

end DerivedFreeModel

end

end AlgebraicGeometry

end

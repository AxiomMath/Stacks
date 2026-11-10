module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.FiniteTrace
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples

/-!
# The trace of `1` along a finite locally free morphism of constant rank

Let `f : X ⟶ P` be a finite, flat morphism of finite presentation, so that the trace
`Trace_f : f_*𝒪_X ⟶ 𝒪_P` (`AlgebraicGeometry.Scheme.Hom.finiteTrace`) is defined. If `f_*𝒪_X`
is finite locally free of constant rank `e`
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, Stacks 01C6 (3)), then
`Trace_f(1) = e` on every open of `P`.

On an affine open `W` over which `f_*𝒪_X` is free of rank `e`, the trace of `1` is the trace of
the identity of the free module `Γ(P, W)^e`, which is `e`. These opens cover `P`, and `𝒪_P` is a
sheaf, so the equality holds on every open.

## Main results

* `Stacks.WeilDeRham.finiteTrace_app_one_of_linearEquiv`: on an affine open `W` with
  `Γ(X, f⁻¹W) ≅ Γ(P, W)^e`, `Trace_f(1) = e`.
* `Stacks.WeilDeRham.nonempty_linearEquiv_sections_of_le`: the sections of a sheaf of modules
  over an open contained in a member of a local free presentation of rank `e` are free of rank
  `e`.
* `Stacks.WeilDeRham.finiteTrace_app_one`: **`Trace_f(1) = e`** on every open of `P`, when
  `f_*𝒪_X` is finite locally free of rank `e`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.WeilDeRham

variable {X P : Scheme.{u}} (f : X ⟶ P) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- **The trace of `1` over an affine open on which `f_*𝒪_X` is free of rank `e` is `e`.** The
trace of `1` is the trace of the identity of the finite projective module `Γ(X, f⁻¹W)`, which is
computed on the free module `Γ(P, W)^e` it is isomorphic to. -/
theorem finiteTrace_app_one_of_linearEquiv (W : P.Opens) (hW : IsAffineOpen W) (e : ℕ)
    (φ : letI := (f.app W).hom.toAlgebra
      Γ(X, f ⁻¹ᵁ W) ≃ₗ[Γ(P, W)] (Fin e → Γ(P, W))) :
    (show Γ(P, W) from (f.finiteTrace).app W (1 : Γ(X, f ⁻¹ᵁ W))) = (e : Γ(P, W)) := by
  let := (f.app W).hom.toAlgebra
  have := f.moduleFinite_app W hW
  have := f.moduleProjective_app W hW
  refine (f.finiteTrace_app_of_isAffineOpen W hW 1).trans ?_
  change Stacks.Discriminant.finiteProjectiveTrace Γ(P, W) Γ(X, f ⁻¹ᵁ W)
    (Algebra.lmul Γ(P, W) Γ(X, f ⁻¹ᵁ W) 1) = _
  rw [map_one, Module.End.one_eq_id,
    Stacks.Discriminant.finiteProjectiveTrace_eq_trace_of_split Γ(P, W) Γ(X, f ⁻¹ᵁ W)
      (Fin e → Γ(P, W)) φ.symm.toLinearMap φ.toLinearMap (by ext; simp)]
  have hid : φ.toLinearMap.comp (LinearMap.id.comp φ.symm.toLinearMap) = LinearMap.id := by
    ext; simp
  rw [hid, LinearMap.trace_eq_matrix_trace Γ(P, W) (Pi.basisFun Γ(P, W) (Fin e)),
    LinearMap.toMatrix_id, Matrix.trace_one, Fintype.card_fin]

/-- **Sections of a locally free sheaf of modules over a small open are free.** If `q` is a
local free presentation of a sheaf of modules `M` on `P` whose basis over the member `q.X i` has
`e` elements, then for every open `W ≤ q.X i` the sections `M(W)` are free of rank `e` over
`𝒪_P(W)`. -/
theorem nonempty_linearEquiv_sections_of_le (M : _root_.SheafOfModules.{u} P.ringCatSheaf)
    (e : ℕ) (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (i : q.I) (σ : (q.generators i).I ≃ Fin e) (W : P.Opens) (h : W ≤ q.X i) :
    Nonempty ((Fin e → P.ringCatSheaf.obj.obj (op W)) ≃ₗ[P.ringCatSheaf.obj.obj (op W)]
      M.val.obj (op W)) := by
  classical
  let Y : Over (q.X i) := Over.mk (homOfLE h)
  have : Fintype (q.generators i).I := Fintype.ofEquiv _ σ.symm
  let E₁ := Stacks.SheafOfModules.freeSectionsIso (R := P.ringCatSheaf.over (q.X i))
    (q.generators i).I (op Y)
  let E₂ := (_root_.SheafOfModules.evaluation _ (op Y)).mapIso (asIso (q.generators i).π)
  exact ⟨(LinearEquiv.funCongrLeft _ _ σ.symm).symm ≪≫ₗ (E₁ ≪≫ E₂).toLinearEquiv⟩

/-- **The trace of `1` is `e` over an affine open contained in a member of a local free
presentation of `f_*𝒪_X` of rank `e`.** -/
theorem finiteTrace_app_one_of_le (e : ℕ)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)))
    [q.IsLocallyFreeData] (i : q.I) (σ : (q.generators i).I ≃ Fin e) (W : P.Opens)
    (hW : IsAffineOpen W) (h : W ≤ q.X i) :
    (show Γ(P, W) from (f.finiteTrace).app W (1 : Γ(X, f ⁻¹ᵁ W))) = (e : Γ(P, W)) := by
  obtain ⟨L⟩ := nonempty_linearEquiv_sections_of_le _ e q i σ W h
  let := (f.app W).hom.toAlgebra
  exact finiteTrace_app_one_of_linearEquiv f W hW e
    { toFun := fun b => L.symm b
      invFun := fun v => L v
      map_add' := fun a b => L.symm.map_add a b
      map_smul' := fun a b => L.symm.map_smul a b
      left_inv := fun b => L.apply_symm_apply b
      right_inv := fun v => L.symm_apply_apply v }

/-- **`Trace_f(1) = e` when `f_*𝒪_X` is finite locally free of rank `e`.** Let `f : X ⟶ P` be
finite, flat and of finite presentation, with `f_*𝒪_X` finite locally free of constant rank `e`
(Stacks 01C6 (3)). Then the trace `Trace_f : f_*𝒪_X ⟶ 𝒪_P` carries the unit section over every
open `U` of `P` to `e`. -/
theorem finiteTrace_app_one (e : ℕ)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (U : P.Opens) :
    (show Γ(P, U) from (f.finiteTrace).app U (1 : Γ(X, f ⁻¹ᵁ U))) = (e : Γ(P, U)) := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let ι := {p : P.affineOpens × q.I // (p.1 : P.Opens) ≤ U ∧ (p.1 : P.Opens) ≤ q.X p.2}
  refine TopCat.Sheaf.eq_of_locally_eq' P.sheaf (fun j : ι => (j.1.1 : P.Opens)) U
    (fun j => homOfLE j.2.1) ?_ _ _ fun j => ?_
  · intro x hx
    obtain ⟨V, g, ⟨i, ⟨g'⟩⟩, hxV⟩ := q.coversTop U x hx
    obtain ⟨W, hW, hxW, hWV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens) hxV
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨(⟨W, hW⟩, i), hWV.trans g.le, hWV.trans g'.le⟩, hxW⟩
  · have hnat := PresheafOfModules.naturality_apply (f.finiteTrace).val (homOfLE j.2.1).op
      (1 : Γ(X, f ⁻¹ᵁ U))
    have h1 : ((Scheme.Modules.pushforward f).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)).val.map (homOfLE j.2.1).op
          (1 : Γ(X, f ⁻¹ᵁ U)) = (1 : Γ(X, f ⁻¹ᵁ (j.1.1 : P.Opens))) :=
      map_one (X.presheaf.map (homOfLE (f.preimage_mono j.2.1)).op).hom
    refine hnat.symm.trans ((congrArg _ h1).trans ?_)
    refine (finiteTrace_app_one_of_le f e q j.1.2 (hr j.1.2).some j.1.1 j.1.1.2 j.2.2).trans ?_
    exact (map_natCast (P.presheaf.map (homOfLE j.2.1).op).hom e).symm

end Stacks.WeilDeRham

end

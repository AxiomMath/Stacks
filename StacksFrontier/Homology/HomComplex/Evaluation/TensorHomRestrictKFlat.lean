module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.RelativelyPerfect.CochainBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatResolution
public import StacksFrontier.Homology.Tor.KFlatResolutionSingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly

/-!
# The derived tensor--Hom diagonal with a tensor factor K-flat over a subring

Let `ψ : S →+* R` be a flat ring map.  The derived tensor--Hom diagonal

`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)`

of `D(R)` is an isomorphism when `K` is represented by a bounded below complex whose
*restriction to `S`* is K-flat, and `L` and `M` are base changes along `ψ` of complexes of
`S`-modules, `L` from a bounded one and `M` from a bounded above complex of finite free modules.

This is a situation outside
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`: there the
tensor factor is required to be *extended* from a K-flat complex over the subring; here only its
restriction is required to be K-flat over the subring, and the other two arguments are extended
instead.

## Proof

Let `p : P ⟶ W` be a K-flat resolution of the representative `W` of `K`.  The chain-level
tensor--Hom map `θ` is an isomorphism at `(W, L, M)`, by the boundedness hypotheses, and its
naturality in the tensor factor compares it with `θ` at `(P, L, M)`.  So `θ` at `(P, L, M)` is a
quasi-isomorphism as soon as `p ▷ L` and `p ▷ Hom(M, L)` are.  Both `L` and `Hom(M, L)` are base
changes along `ψ` -- the second because `M` is finite free in each degree and `L` is bounded
(`StacksDraft.RelativelyPerfect.homCochainBaseChange_bijective`) -- and `p ▷ ψ^* V` is a
quasi-isomorphism for every complex `V` of `S`-modules: resolving `V` by a K-flat `V'`, the three
other sides of the square are quasi-isomorphisms, the last because the restriction of `W` to `S`
is K-flat (`CochainComplex.DerivedTensor.quasiIso_tleftCochain_map_extendScalars`).

## Main results

* `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_restrictKFlat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedTensorHomDiagonal

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S]

/-- In a commuting square whose other two sides are quasi-isomorphisms, the two remaining sides
are quasi-isomorphisms simultaneously. -/
private theorem quasiIso_iff_of_comp_eq {A B C D : CochainComplex (ModuleCat.{u} R) ℤ}
    {f : A ⟶ B} {g : B ⟶ D} {f' : A ⟶ C} {g' : C ⟶ D} (h : f ≫ g = f' ≫ g')
    [QuasiIso f'] [QuasiIso g'] : QuasiIso f ↔ QuasiIso g := by
  have : QuasiIso (f ≫ g) := by
    rw [h]
    infer_instance
  exact ⟨fun _ => (quasiIso_iff_comp_left f g).1 this,
    fun _ => (quasiIso_iff_comp_right f g).1 this⟩

/-- Tensoring on the right with a base change along a flat map: if the restriction to `S` of `W`
is K-flat, then for any K-flat resolution `p : P ⟶ W` and any complex `V` of `S`-modules,
`p ▷ (R ⊗_S V)` is a quasi-isomorphism. -/
theorem quasiIso_whiskerRight_extendScalars_of_restrictKFlat (ψ : S →+* R) (hψ : ψ.Flat)
    {W P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hW : CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u, u, u} ψ).obj W))
    (p : P ⟶ W) [QuasiIso p] (hP : CochainComplex.KFlat.{u, u} P)
    (V : CochainComplex (ModuleCat.{u} S) ℤ) :
    QuasiIso (p ▷ (CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj V) := by
  obtain ⟨V', q, hV', -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} V
  have := hq
  let ext := CochainComplex.extendScalarsLarge.{u, u, u} ψ
  have hV'R : CochainComplex.KFlat.{u, u} (ext.obj V') := _root_.kFlat_baseChange ψ V' hV'
  have h1 : QuasiIso (p ▷ ext.obj V') :=
    CochainComplex.DerivedTensor.quasiIso_tright_map.{u, u} (ext.obj V') hV'R p
  have : (ModuleCat.extendScalars.{u, u, u} ψ).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} ψ hψ
  have hq' : QuasiIso (ext.map q) := by
    show QuasiIso (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q)
    infer_instance
  have h2 : QuasiIso (P ◁ ext.map q) :=
    CochainComplex.DerivedTensor.quasiIso_tleftCochain_map_of_kFlat P hP (ext.map q) hq'
  have h3 : QuasiIso (W ◁ ext.map q) :=
    CochainComplex.DerivedTensor.quasiIso_tleftCochain_map_extendScalars ψ W hW q hq
  exact (quasiIso_iff_of_comp_eq (MonoidalCategory.whisker_exchange p (ext.map q))).1 h2

/-- Extension of scalars preserves a strict upper bound on a complex. -/
theorem isStrictlyLE_extendScalarsLarge (ψ : S →+* R) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (d : ℤ) [P.IsStrictlyLE d] :
    ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj P).IsStrictlyLE d :=
  (CochainComplex.isStrictlyLE_iff _ d).mpr fun i hi =>
    (ModuleCat.extendScalars ψ).map_isZero (P.isZero_of_isStrictlyLE d i hi)

/-- Extension of scalars preserves a strict lower bound on a complex. -/
theorem isStrictlyGE_extendScalarsLarge (ψ : S →+* R) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (a : ℤ) [P.IsStrictlyGE a] :
    ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj P).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    (ModuleCat.extendScalars ψ).map_isZero (P.isZero_of_isStrictlyGE a i hi)

/-- The base change of the Hom complex out of a bounded above complex of finite free modules into
a bounded complex is the Hom complex between the base changes. -/
def homComplexBaseChangeIso (ψ : S →+* R) (F J : CochainComplex (ModuleCat.{u} S) ℤ) (b c : ℤ)
    [J.IsStrictlyGE b] [J.IsStrictlyLE c]
    [∀ i, Module.Finite S (F.X i)] [∀ i, Module.Free S (F.X i)] :
    (CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj (CochainComplex.HomComplexR S F J) ≅
      CochainComplex.HomComplexR R ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj F)
        ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj J) := by
  have : ∀ n, IsIso ((StacksDraft.RelativelyPerfect.homComplexBaseChange ψ F J).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (StacksDraft.RelativelyPerfect.homCochainBaseChange_bijective ψ F J b c n)
  have h : IsIso (StacksDraft.RelativelyPerfect.homComplexBaseChange ψ F J) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact @asIso _ _ _ _ (StacksDraft.RelativelyPerfect.homComplexBaseChange ψ F J) h

/-- Extension of scalars of a finite module is finite. -/
theorem finite_extendScalars (ψ : S →+* R) (N : ModuleCat.{u} S) [Module.Finite S N] :
    Module.Finite R ((ModuleCat.extendScalars.{u, u, u} ψ).obj N) := by
  let := ψ.toAlgebra
  show Module.Finite R (R ⊗[S] N)
  infer_instance

/-- Extension of scalars of a free module is free. -/
theorem free_extendScalars (ψ : S →+* R) (N : ModuleCat.{u} S) [Module.Free S N] :
    Module.Free R ((ModuleCat.extendScalars.{u, u, u} ψ).obj N) := by
  let := ψ.toAlgebra
  show Module.Free R (R ⊗[S] N)
  infer_instance

/-- **The derived tensor--Hom diagonal with a tensor factor K-flat over a subring.**  Let
`ψ : S →+* R` be flat, let `W` be a bounded below complex of `R`-modules whose restriction to `S`
is K-flat, let `X` be a bounded complex of `S`-modules and `F` a bounded above complex of finite
free `S`-modules.  Then the derived tensor--Hom diagonal of `D(R)` at
`(W, R ⊗_S X, R ⊗_S F)` is an isomorphism. -/
theorem isIso_derivedTensorHomDiagonal_of_restrictKFlat (ψ : S →+* R) (hψ : ψ.Flat)
    (W : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) [W.IsStrictlyGE a]
    (hW : CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u, u, u} ψ).obj W))
    (X : CochainComplex (ModuleCat.{u} S) ℤ) (b c : ℤ) [X.IsStrictlyGE b] [X.IsStrictlyLE c]
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    [∀ i, Module.Finite S (F.X i)] [∀ i, Module.Free S (F.X i)] :
    IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal (DerivedCategory.Q.obj W)
      (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj X))
      (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj F))) := by
  let ext := CochainComplex.extendScalarsLarge.{u, u, u} ψ
  let L := ext.obj X
  let M := ext.obj F
  have := isStrictlyGE_extendScalarsLarge ψ X b
  have := isStrictlyLE_extendScalarsLarge ψ F d
  have hMfin : ∀ i, Module.Finite R (M.X i) := fun i => finite_extendScalars ψ (F.X i)
  have hMfree : ∀ i, Module.Free R (M.X i) := fun i => free_extendScalars ψ (F.X i)
  have hMproj : ∀ i, Projective (M.X i) := fun i =>
    ModuleCat.projective_of_categoryTheory_projective _
  have hMproj' : ∀ i, Module.Projective R (M.X i) := fun i => inferInstance
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} W
  have := hp
  have hL : QuasiIso (p ▷ L) :=
    quasiIso_whiskerRight_extendScalars_of_restrictKFlat ψ hψ hW p hP X
  have hH0 : QuasiIso (p ▷ ext.obj (CochainComplex.HomComplexR S F X)) :=
    quasiIso_whiskerRight_extendScalars_of_restrictKFlat ψ hψ hW p hP _
  have hH : QuasiIso (p ▷ CochainComplex.HomComplexR R M L) :=
    (CochainComplex.DerivedTensor.quasiIso_whiskerRight_iff_of_iso (L := ext.obj
      (CochainComplex.HomComplexR S F X)) (L' := CochainComplex.HomComplexR R M L) p
      (homComplexBaseChangeIso ψ F X b c)).2 hH0
  have hθW : IsIso (Stacks.HomComplex.TensorHomComparison.theta W L M) :=
    isIso_theta_of_boundedBelow W L M a b d
  have hθW' : QuasiIso (Stacks.HomComplex.TensorHomComparison.theta W L M) := quasiIso_of_isIso _
  have hHom : QuasiIso (Stacks.HomComplex.TensorHomComparison.HomCxMap M M (P ⊗ L) (W ⊗ L)
      (𝟙 M) (p ▷ L)) :=
    StacksDraft.DerivedHom.ProjectiveHomComparison.quasiIso_homCxMap
      StacksDraft.DerivedHom.projectiveHomComparison M (P ⊗ L) (W ⊗ L) d (p ▷ L)
  have hsq := Stacks.HomComplex.TensorHomComparison.theta_natural_K P W L M p
  have hθP : QuasiIso (Stacks.HomComplex.TensorHomComparison.theta P L M) :=
    (quasiIso_iff_of_comp_eq hsq).2 hHom
  have := isIso_diagonal_of_projective_quasiIso_theta P L M d hP
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) p).2 hp
  exact isIso_diagonal_of_iso (asIso (DerivedCategory.Q.map p)).symm (Iso.refl _) (Iso.refl _)

end

end Stacks.DerivedTensorHomDiagonal

end

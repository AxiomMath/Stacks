module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedQuasicoherentFirstOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor

/-!
# Quasi-coherent cohomology descends along a finite-order thickening

Let `Z ⊂ X'` be a finite-order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X'`, and let `K'` be an object of `D(𝒪_{X'})` whose derived pullback `Li^*K'` lies in
`D_QCoh(𝒪_Z)`. Then `K'` lies in `D_QCoh(𝒪_{X'})`. This is the first paragraph of the proof of
Stacks 0DL3.

## Main results

* `derivedCategoryB_smallEtaleDerivedModulePullback_of_comp_eq`: the pullback along a composite
  `f ≫ g` lies in `D_QCoh` when the pullback along `g` does.
* `qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFiniteOrderThickening`: for a
  finite-order thickening `i : Z ⟶ X'`, if `Li^*K'` lies in `D_QCoh(𝒪_Z)` then `K'` lies in
  `D_QCoh(𝒪_{X'})`.

## Implementation notes

As in the source, reduce to a first-order thickening by Section 05ZJ: an `n`th-order thickening is
filtered by closed subspaces `Z = X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n = X'`, each `X_k ⊂ X_{k+1}` a first-order
thickening (`AlgebraicGeometry.Space.exists_firstOrderThickening_filtration`). By induction on `k`
the derived pullback of `K'` to `X_k` lies in `D_QCoh`: the step is the first-order case,
`qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFirstOrderThickening`, applied
on `X_{k+1}` to the pullback of `K'` there, whose further pullback to `X_k` is the pullback of
`K'` to `X_k` along a factorization of the inclusions (Stacks 08F4 moves `D_QCoh` along the
comparison morphism). At `k = n` the inclusion `X_n ⟶ X'` has a section, through which `K'` is
recovered.

## References

* [Stacks Project, Tag 0DL3](https://stacks.math.columbia.edu/tag/0DL3)
* [Stacks Project, Section 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A derived-category object isomorphic to one with quasi-coherent cohomology has quasi-coherent
cohomology. -/
private theorem derivedCategoryB_isQuasicoherentOnSite_of_iso {A : AlgebraicSpaces B S hS}
    {K L : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O))}
    (e : L ≅ K)
    (hL : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O))) L) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O))) K :=
  fun n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hL n)

/-- If a morphism `k` factors as `f ≫ g`, and the derived pullback of `K` along `g` has
quasi-coherent cohomology, so does its derived pullback along `k`: it is the derived pullback
along `f` of an object of `D_QCoh` (Stacks 08F4). -/
theorem derivedCategoryB_smallEtaleDerivedModulePullback_of_comp_eq
    {A A' C : AlgebraicSpaces B S hS} (f : A ⟶ A') (g : A' ⟶ C) (k : A ⟶ C) (hk : f ≫ g = k)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS C)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A'.1 A'.2).O)))
      ((smallEtaleDerivedPullbackData B S hS).pull g |>.obj K)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O)))
      ((smallEtaleDerivedPullbackData B S hS).pull k |>.obj K) := by
  exact derivedCategoryB_isQuasicoherentOnSite_of_iso B S hS
    (((smallEtaleDerivedPullbackData B S hS).triangle hk).app K).symm
    (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS f _ hK)

/-- If `V ∩ W ⊂ W` is a first-order thickening of closed subspaces of `X'` and the derived
pullback of `K` to `V` has quasi-coherent cohomology, so does its derived pullback to `W`. -/
theorem qcohDerived_smallEtaleDerivedPullback_of_isFirstOrderThickening_preimage
    {X' : AlgebraicSpaces B S hS} (V W : ClosedSubspaces B S hS X'.1)
    (hVW : IsFirstOrderThickening B S hS ⟨W.1.toFunctor, W.2.1⟩ (V.1.preimage W.1.ι))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1.toFunctor V.2.1).O)))
      ((smallEtaleDerivedPullbackData B S hS).pull (subspaceInclusion B S hS X' V) |>.obj K)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1.toFunctor W.2.1).O)))
      ((smallEtaleDerivedPullbackData B S hS).pull (subspaceInclusion B S hS X' W) |>.obj K) := by
  let P : ClosedSubspaces B S hS W.1.toFunctor := ⟨V.1.preimage W.1.ι, hVW.1.1⟩
  have hrange : Subfunctor.range (P.1.ι ≫ W.1.ι) ≤ V.1 := by
    rintro T _ ⟨x, rfl⟩
    exact x.2
  let e : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V.1.toFunctor, V.2.1⟩ :=
    ObjectProperty.homMk (Subfunctor.lift (P.1.ι ≫ W.1.ι) hrange)
  have hsq : e ≫ subspaceInclusion B S hS X' V =
      subspaceInclusion B S hS ⟨W.1.toFunctor, W.2.1⟩ P ≫ subspaceInclusion B S hS X' W :=
    ObjectProperty.hom_ext _ rfl
  exact qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFirstOrderThickening
    B S hS (Y := ⟨W.1.toFunctor, W.2.1⟩) P hVW
    ((smallEtaleDerivedPullbackData B S hS).pull (subspaceInclusion B S hS X' W) |>.obj K)
    (derivedCategoryB_isQuasicoherentOnSite_of_iso B S hS (A := ⟨P.1.toFunctor, P.2.1⟩)
      (((smallEtaleDerivedPullbackData B S hS).compIso _ _).app K)
      (derivedCategoryB_smallEtaleDerivedModulePullback_of_comp_eq B S hS e _ _ hsq K hK))

/-- **Quasi-coherent cohomology descends along a finite-order thickening.** Let `Z ⊂ X'` be a
finite-order thickening of algebraic spaces with inclusion `i`, and let `K' ∈ D(𝒪_{X'})`. If
`Li^*K'` has quasi-coherent cohomology sheaves, so does `K'`. -/
theorem qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFiniteOrderThickening
    {X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
    (hZ : IsFiniteOrderThickening B S hS X' Z.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK :
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (subspaceInclusion B S hS X' Z)
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1.toFunctor Z.2.1).O)))
        ((smallEtaleDerivedModulePullback B S hS (subspaceInclusion B S hS X' Z)).obj K)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)))
      K := by
  obtain ⟨n, hn⟩ := hZ
  obtain ⟨Xs, -, -, -, h0, htop, -, hfo⟩ := exists_firstOrderThickening_filtration B S hS X' hn
  let QCs : ClosedSubspaces B S hS X'.1 → Prop := fun W => DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1.toFunctor W.2.1).O)))
    ((smallEtaleDerivedPullbackData B S hS).pull (subspaceInclusion B S hS X' W) |>.obj K)
  have hall : ∀ k, QCs (Xs k) := fun k => Nat.rec ((congrArg QCs (Subtype.ext h0)).mpr hK)
    (fun k hk => qcohDerived_smallEtaleDerivedPullback_of_isFirstOrderThickening_preimage B S hS
      (Xs k) (Xs (k + 1)) (hfo k) K hk) k
  have hrange : Subfunctor.range (𝟙 X'.1) ≤ (Xs n).1 := htop ▸ le_top
  let s : X' ⟶ ⟨(Xs n).1.toFunctor, (Xs n).2.1⟩ :=
    ObjectProperty.homMk (Subfunctor.lift (𝟙 X'.1) hrange)
  have hs : s ≫ subspaceInclusion B S hS X' (Xs n) = 𝟙 X' :=
    ObjectProperty.hom_ext _ rfl
  exact derivedCategoryB_isQuasicoherentOnSite_of_iso B S hS
    (((smallEtaleDerivedPullbackData B S hS).idIso X').app K)
    (derivedCategoryB_smallEtaleDerivedModulePullback_of_comp_eq B S hS s _ _ hs K (hall n))

end AlgebraicGeometry.Space

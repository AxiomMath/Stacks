module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulKFlat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes

/-!
# The derived pullback of a Koszul complex

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `t_1, …, t_r` be global
sections of `𝒪` and let `g_1, …, g_r` be global sections of `𝒪'` with `g_i = f^♯(t_i)`. Then

`Lf^*K(𝒪, t_1^{n+1}, …, t_r^{n+1}) ≅ K(𝒪', g_1^{n+1}, …, g_r^{n+1})` in `D(𝒪')`,

compatibly with the transition maps of the two Koszul towers.

The Koszul complex is bounded with terms finite direct sums of copies of the structure sheaf, so
it is K-flat with flat terms and the derived pullback is computed by the degreewise pullback
(`Stacks.Sheaves.DerivedPullback.flatPullbackIso`, the computation assertion of
[Stacks, Tag 06YY]); the degreewise pullback is identified with the other Koszul complex by
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerComplexIso`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerComplexIso`:
  **`Lf^*K(𝒪, t^{n+1}) ≅ K(𝒪', g^{n+1})`** in `D(𝒪')`.
* `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerComplexIso_naturality`: it is
  compatible with the transition maps of the two towers.
* `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerSystemIso`: the same as an isomorphism
  of towers in `D(𝒪')`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasFiniteBiproducts_sheafOfModules
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

section Derived

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

include hg in
/-- **`Lf^*K(𝒪, t^{n+1}) ≅ K(𝒪', g^{n+1})`.** The Koszul complex is K-flat with flat terms, so
its derived pullback is the class of its degreewise pullback, and that is the Koszul complex on
the pushed-forward sections. -/
def derivedPullbackKoszulPowerComplexIso (n : ℕ) :
    (derivedPullback.{u} f.toRingedToposSiteHom).obj
        (DerivedCategory.Q.obj (koszulPowerComplex Y t n)) ≅
      DerivedCategory.Q.obj (koszulPowerComplex X g n) :=
  Stacks.Sheaves.DerivedPullback.flatPullbackIso f.toRingedToposSiteHom f.isMorphismOfSites
      (koszulPowerComplex Y t n) (isKFlat_koszulPowerComplex Y t n)
      (fun i => isFlat_of_isFiniteFreeSummand Y ((koszulPowerComplex Y t n).X i)
        (isFiniteFreeSummand_koszulPowerComplex_X Y t n i)) ≪≫
    DerivedCategory.Q.mapIso (pullbackKoszulPowerComplexIso f t g hg n)

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- **The identification is compatible with the transition maps of the two Koszul towers.** -/
theorem derivedPullbackKoszulPowerComplexIso_naturality (n : ℕ) :
    (derivedPullback.{u} f.toRingedToposSiteHom).map
          (DerivedCategory.Q.map (koszulPowerComplexMap Y t n)) ≫
        (derivedPullbackKoszulPowerComplexIso f t g hg (n + 1)).hom =
      (derivedPullbackKoszulPowerComplexIso f t g hg n).hom ≫
        DerivedCategory.Q.map (koszulPowerComplexMap X g n) := by
  dsimp only [derivedPullbackKoszulPowerComplexIso, Iso.trans_hom, Functor.mapIso_hom]
  have hflat (m : ℕ) (i : ℤ) := isFlat_of_isFiniteFreeSummand Y ((koszulPowerComplex Y t m).X i)
    (isFiniteFreeSummand_koszulPowerComplex_X Y t m i)
  rw [← Category.assoc, Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality
      f.toRingedToposSiteHom f.isMorphismOfSites (koszulPowerComplexMap Y t n)
      (isKFlat_koszulPowerComplex Y t n) (isKFlat_koszulPowerComplex Y t (n + 1))
      (hflat n) (hflat (n + 1)),
    Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    pullbackKoszulPowerComplexIso_naturality f t g hg n]

include hg in
/-- **The derived pullback carries one Koszul tower to the other**, compatibly with the
transition maps. -/
def derivedPullbackKoszulPowerSystemMap :
    koszulPowerSystem Y t ⋙ DerivedCategory.Q ⋙
        derivedPullback.{u} f.toRingedToposSiteHom ⟶
      koszulPowerSystem X g ⋙ DerivedCategory.Q :=
  NatTrans.ofSequence
    (fun n => (derivedPullbackKoszulPowerComplexIso f t g hg n).hom) fun n => by
    change (derivedPullback.{u} f.toRingedToposSiteHom).map (DerivedCategory.Q.map
          ((koszulPowerSystem Y t).map (homOfLE n.le_succ))) ≫
        (derivedPullbackKoszulPowerComplexIso f t g hg (n + 1)).hom =
      (derivedPullbackKoszulPowerComplexIso f t g hg n).hom ≫
        DerivedCategory.Q.map ((koszulPowerSystem X g).map (homOfLE n.le_succ))
    rw [show (koszulPowerSystem Y t).map (homOfLE n.le_succ) = koszulPowerComplexMap Y t n from
        Functor.ofSequence_map_homOfLE_succ _ n,
      show (koszulPowerSystem X g).map (homOfLE n.le_succ) = koszulPowerComplexMap X g n from
        Functor.ofSequence_map_homOfLE_succ _ n]
    exact derivedPullbackKoszulPowerComplexIso_naturality f t g hg n

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- The natural transformation `derivedPullbackKoszulPowerSystemMap` from the derived pullback of
the Koszul tower on `t` to the Koszul tower on `g` is an isomorphism. -/
theorem isIso_derivedPullbackKoszulPowerSystemMap :
    IsIso (derivedPullbackKoszulPowerSystemMap f t g hg) := by
  have hi (n : ℕ) : IsIso ((derivedPullbackKoszulPowerSystemMap f t g hg).app n) := by
    change IsIso (derivedPullbackKoszulPowerComplexIso f t g hg n).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include hg in
/-- **The derived pullback carries one Koszul tower to the other**, as an isomorphism of towers
in `D(𝒪')`. -/
def derivedPullbackKoszulPowerSystemIso :
    koszulPowerSystem Y t ⋙ DerivedCategory.Q ⋙
        derivedPullback.{u} f.toRingedToposSiteHom ≅
      koszulPowerSystem X g ⋙ DerivedCategory.Q :=
  @asIso _ _ _ _ (derivedPullbackKoszulPowerSystemMap f t g hg)
    (isIso_derivedPullbackKoszulPowerSystemMap f t g hg)

end Derived

end AlgebraicGeometry.RingedSite

end

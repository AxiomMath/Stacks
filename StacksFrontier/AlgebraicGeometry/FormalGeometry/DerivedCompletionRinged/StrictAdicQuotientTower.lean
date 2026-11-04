module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.UnitLawNaturality
public import StacksFrontier.CategoryTheory.Triangulated.MilnorFibreTower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adic quotient tower, strictified

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. The tower of derived reductions
`n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` — `AlgebraicGeometry.RingedSite.adicReductionTower` — is a tower in
`D(𝒪)`, and every construction of a *named* `R lim` takes a tower of honest cochain complexes.
For a K-flat complex `K̃` this file realizes the derived tower as
`F ⋙ DerivedCategory.Q` for the honest tower

`F : ℕᵒᵖ ⥤ CochainComplex (Mod 𝒪) ℤ`, `F n = Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`,

together with the strict cone on `F` whose vertex is `K̃` itself.

## What is strict and what is not

`n ↦ 𝒪/ℐⁿ⁺¹` is an honest tower of sheaves of modules
(`AlgebraicGeometry.RingedSite.adicQuotientTower`), and the total tensor complex is an honest
bifunctor of cochain complexes, so `F` is a composite of functors and nothing is chosen in it.
The only derived-category content is the choice of `K̃`, which is a *parameter* here: every
declaration below takes the K-flat complex and the witness of its K-flatness as arguments, and
no K-flat resolution is invoked.

## The cone comes from `K`, not from `K^∧`

`AlgebraicGeometry.RingedSite.strictAdicAugmentation` has vertex `K̃`, and its `n`-th map is
`K̃ ≅ Tot(K̃ ⊗ 𝒪[0]) ⟶ Tot(K̃ ⊗ (𝒪/ℐⁿ⁺¹)[0])`, i.e. `K̃` tensored with the quotient map
`𝒪 ⟶ 𝒪/ℐⁿ⁺¹`. That is the cone of [Stacks, Tag 0CQH]: the comparison map it induces is the one
whose invertibility is the assertion `K^∧ = R lim (K ⊗^𝐋 𝒪/ℐⁿ)`, and it would be a different
map — and a vacuous one — if the cone were taken out of the completion instead.
`AlgebraicGeometry.RingedSite.Q_strictAdicAugmentation_app` is the statement that pins this
down: the image in `D(𝒪)` of the `n`-th map of the cone is, through the K-flat comparison, the
derived reduction `AlgebraicGeometry.RingedSite.adicQuotientReduction` of `Q K̃` itself.

## Main definitions

* `AlgebraicGeometry.RingedSite.comparisonLeftNatIso` — the K-flat comparison
  `Q K̃ ⊗^𝐋_𝒪 Q L ≅ Q Tot(K̃ ⊗_𝒪 L)` as an isomorphism of **functors** of `L`.
* `AlgebraicGeometry.RingedSite.strictAdicQuotientTower` — the tower `n ↦ (𝒪/ℐⁿ⁺¹)[0]` of
  cochain complexes.
* `AlgebraicGeometry.RingedSite.strictAdicReductionTower` — the tower
  `n ↦ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])` of cochain complexes.
* `AlgebraicGeometry.RingedSite.strictAdicAugmentation` — the strict cone on it with vertex `K̃`.

## Main results

* `AlgebraicGeometry.RingedSite.strictAdicReductionTowerIso` — `F ⋙ DerivedCategory.Q` is the
  tower of derived reductions of `Q K̃`, naturally in `n`.
* `AlgebraicGeometry.RingedSite.Q_strictAdicAugmentation_app` — the image of the strict cone is
  the cone of derived reductions.

## Implementation notes

The K-flat comparison is needed naturally in `L`: without it the identification of `F ⋙ Q`
with the derived tower is available one `n` at a time and not as a natural transformation, which
is what a tower needs. `Stacks.SheafOfModules.DerivedTensorProduct.comparisonLeft` of
`CategoryTheory/Sites/Cohomology/DerivedTensor/Interface.lean` is a family of isomorphisms indexed
by `L` and `comparisonLeft_naturality` is the corresponding equation for a cochain map, so
`CategoryTheory.NatIso.ofComponents` assembles them; the naturality square needed is that field
with the left morphism taken to be `𝟙 K̃`. Compare
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorComparisonNatIso`, the analogous
assembly at the unit complex.

The right unit law used for the vertex of the cone is
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, the one the derived unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso` is built from, and *not* the right unitor
of the monoidal structure on cochain complexes: the proof of
`AlgebraicGeometry.RingedSite.Q_strictAdicAugmentation_app` goes through the derived unit law,
and no comparison of the two unit laws is available.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (X : RingedSite.{u, u, u})

/-! ### The K-flat comparison, naturally in the right factor -/

section Comparison

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)
  (Kt : CochainComplex (Modules X) ℤ) (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt)

/-- **The left K-flat comparison of the derived tensor product, as an isomorphism of functors of
the right factor**: for a K-flat complex `K̃`, the two functors
`L ↦ Q K̃ ⊗^𝐋_𝒪 Q L` and `L ↦ Q Tot(K̃ ⊗_𝒪 L)` on `CochainComplex (Mod 𝒪) ℤ` are isomorphic. -/
def comparisonLeftNatIso :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj Kt) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun L => T.comparisonLeft Kt L hKt) fun {L L'} g => by
    have h := T.comparisonLeft_naturality (𝟙 Kt) g hKt hKt
    rw [DerivedCategory.Q.map_id, T.tensor.map_id, NatTrans.id_app, Category.id_comp] at h
    exact h

/-- The component at `L` of `AlgebraicGeometry.RingedSite.comparisonLeftNatIso` is the left
K-flat comparison `Q K̃ ⊗^𝐋_𝒪 Q L ≅ Q Tot(K̃ ⊗_𝒪 L)`. -/
@[reassoc (attr := simp)]
theorem comparisonLeftNatIso_hom_app (L : CochainComplex (Modules X) ℤ) :
    (comparisonLeftNatIso X T Kt hKt).hom.app L = (T.comparisonLeft Kt L hKt).hom :=
  rfl

/-- The naturality square of `AlgebraicGeometry.RingedSite.comparisonLeftNatIso`, written out:
the image of a cochain map under `Tot(K̃ ⊗ -)` is, through the comparison, the derived tensor
product of `Q K̃` with its image. -/
@[reassoc]
theorem Q_map_tensorComplex_map {L L' : CochainComplex (Modules X) ℤ} (g : L ⟶ L') :
    (T.comparisonLeft Kt L hKt).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map g) =
      (T.tensor.obj (DerivedCategory.Q.obj Kt)).map (DerivedCategory.Q.map g) ≫
        (T.comparisonLeft Kt L' hKt).hom :=
  ((comparisonLeftNatIso X T Kt hKt).hom.naturality g).symm

end Comparison

/-! ### The honest towers -/

variable (I : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- The complex `(𝒪/ℐⁿ⁺¹)[0]`: the quotient of the structure sheaf by the `(n+1)`-st power of a
sheaf of ideals, placed in degree zero.

This exists as a definition of its own, rather than as `(strictAdicQuotientTower X I).obj ⟨n⟩` or
as the single-complex functor applied to `Stacks.Sites.adicQuotientModule`, so that the statements
below mention *one* spelling of it. `AlgebraicGeometry.RingedSite.Modules` and the
`SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))` that
`Stacks.Sites.adicQuotientModule` is valued in are definitionally but not reducibly equal, so a
goal mixing two spellings is not type-correct at `implicit` transparency and neither `rw` nor
`simp` fires on it. -/
@[sga "2 VI 2.2" "partial"]
def strictAdicQuotientObj (n : ℕ) : CochainComplex (Modules X) ℤ :=
  (CochainComplex.singleFunctor (Modules X) 0).obj
    (Stacks.Sites.adicQuotientModule (X := X) I (n + 1))

/-- The projection `𝒪[0] ⟶ (𝒪/ℐⁿ⁺¹)[0]`. -/
def strictAdicQuotientπ (n : ℕ) :
    Stacks.SheafOfModules.unitCochainComplex X ⟶ strictAdicQuotientObj X I n :=
  (CochainComplex.singleFunctor (Modules X) 0).map
    (Stacks.Sites.adicQuotientModuleπ (X := X) I (n + 1))

/-- The transition map `(𝒪/ℐⁿ⁺²)[0] ⟶ (𝒪/ℐⁿ⁺¹)[0]`. -/
def strictAdicQuotientMap (n : ℕ) :
    strictAdicQuotientObj X I (n + 1) ⟶ strictAdicQuotientObj X I n :=
  (CochainComplex.singleFunctor (Modules X) 0).map
    (Stacks.Sites.adicQuotientModuleMap (X := X) I (Nat.le_succ (n + 1)))

/-- **The projections are compatible with the transition maps**, in degree zero. -/
@[reassoc]
theorem strictAdicQuotientπ_comp_map (n : ℕ) :
    strictAdicQuotientπ X I (n + 1) ≫ strictAdicQuotientMap X I n =
      strictAdicQuotientπ X I n :=
  (((CochainComplex.singleFunctor (Modules X) 0).map_comp _ _).symm).trans
    (congrArg (CochainComplex.singleFunctor (Modules X) 0).map
      (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap I (Nat.le_succ (n + 1))))

/-- The tower `n ↦ (𝒪/ℐⁿ⁺¹)[0]` of quotients of the structure sheaf by the positive powers of a
sheaf of ideals, placed in degree zero: `AlgebraicGeometry.RingedSite.adicQuotientTower`
followed by the degree-zero single-complex functor. -/
def strictAdicQuotientTower : ℕᵒᵖ ⥤ CochainComplex (Modules X) ℤ :=
  adicQuotientTower X I ⋙ CochainComplex.singleFunctor (Modules X) 0

/-- The successive transition map of the strict tower is the transition map of the quotients,
placed in degree zero. -/
theorem strictAdicQuotientTower_map_succ (n : ℕ) :
    (strictAdicQuotientTower X I).map (homOfLE (Nat.le_succ n)).op =
      strictAdicQuotientMap X I n :=
  congrArg (CochainComplex.singleFunctor (Modules X) 0).map (adicQuotientTower_map_succ X I n)

/-- **The adic quotient tower, strictified**: the tower `n ↦ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])` of honest
cochain complexes, for a complex `K̃`.

Its image under `DerivedCategory.Q` is the tower of derived reductions of `Q K̃` as soon as `K̃`
is K-flat; that is `AlgebraicGeometry.RingedSite.strictAdicReductionTowerIso`. -/
def strictAdicReductionTower (Kt : CochainComplex (Modules X) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules X) ℤ :=
  strictAdicQuotientTower X I ⋙ (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt

/-- The `n`-th object of the strictified tower is `Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`. -/
theorem strictAdicReductionTower_obj (Kt : CochainComplex (Modules X) ℤ) (n : ℕ) :
    (strictAdicReductionTower X I Kt).obj ⟨n⟩ =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).obj
        (strictAdicQuotientObj X I n) :=
  rfl

/-- The successive transition map of the strictified tower is `K̃` tensored with the transition
map of the quotients. -/
theorem strictAdicReductionTower_map_succ (Kt : CochainComplex (Modules X) ℤ) (n : ℕ) :
    (strictAdicReductionTower X I Kt).map (homOfLE (Nat.le_succ n)).op =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map
        (strictAdicQuotientMap X I n) :=
  congrArg ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map
    (strictAdicQuotientTower_map_succ X I n)

/-! ### Identification with the tower of derived reductions -/

/-- **The strictified tower is the tower of derived reductions**, for an arbitrary derived
tensor product: the image of `AlgebraicGeometry.RingedSite.strictAdicReductionTower` under
`DerivedCategory.Q` is the tower `n ↦ Q K̃ ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` formed with `T`, naturally in the
index. -/
def strictAdicReductionTowerIsoOf (T : Stacks.SheafOfModules.DerivedTensorProduct X)
    (Kt : CochainComplex (Modules X) ℤ) (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) :
    adicQuotientTower X I ⋙ DerivedCategory.singleFunctor (Modules X) 0 ⋙
        T.tensor.obj (DerivedCategory.Q.obj Kt) ≅
      strictAdicReductionTower X I Kt ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft (strictAdicQuotientTower X I) (comparisonLeftNatIso X T Kt hKt)

/-- **The strictified tower is the tower of derived reductions.** For a K-flat complex `K̃` the
image of `AlgebraicGeometry.RingedSite.strictAdicReductionTower` under `DerivedCategory.Q` is
`AlgebraicGeometry.RingedSite.adicReductionTower` at `Q K̃`, naturally in the index. -/
def strictAdicReductionTowerIso (Kt : CochainComplex (Modules X) ℤ)
    (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) :
    adicReductionTower X I (DerivedCategory.Q.obj Kt) ≅
      strictAdicReductionTower X I Kt ⋙ DerivedCategory.Q :=
  strictAdicReductionTowerIsoOf X I (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
    Kt hKt

/-- The component at `n` of `AlgebraicGeometry.RingedSite.strictAdicReductionTowerIso` is the
left K-flat comparison `Q K̃ ⊗^𝐋_𝒪 Q (𝒪/ℐⁿ⁺¹)[0] ≅ Q Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])` for the
canonical derived tensor product. -/
@[simp]
theorem strictAdicReductionTowerIso_hom_app (Kt : CochainComplex (Modules X) ℤ)
    (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) (n : ℕᵒᵖ) :
    (strictAdicReductionTowerIso X I Kt hKt).hom.app n =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft Kt
        ((strictAdicQuotientTower X I).obj n) hKt).hom :=
  rfl

/-! ### The strict cone -/

/-- The `n`-th map of the strict cone on the strictified tower: the right unit law
`K̃ ≅ Tot(K̃ ⊗_𝒪 𝒪[0])` followed by `K̃` tensored with the quotient map `𝒪 ⟶ 𝒪/ℐⁿ⁺¹`.

The unit law used is `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, the one the
derived unit law of [Stacks, Tag 06YU] is built from. -/
def strictAdicAugmentationApp (Kt : CochainComplex (Modules X) ℤ) (n : ℕ) :
    Kt ⟶ (strictAdicReductionTower X I Kt).obj ⟨n⟩ :=
  (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv ≫
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map (strictAdicQuotientπ X I n)

/-- **The maps of the strict cone are compatible with the transition maps of the tower, on the
nose.** The compatibility is that of the projections `𝒪 ⟶ 𝒪/ℐⁿ` with the transition maps
`𝒪/ℐⁿ⁺¹ ⟶ 𝒪/ℐⁿ`, tensored with `K̃`.

Both steps are `Eq.trans`ed rather than rewritten: the two sides of
`AlgebraicGeometry.RingedSite.strictAdicReductionTower_map_succ` are the tower's structure map
and a formula in the quotient maps, whose types are definitionally but not reducibly equal, so
a `rw` leaves a goal that is not type-correct at `implicit` transparency. -/
theorem strictAdicAugmentationApp_naturality (Kt : CochainComplex (Modules X) ℤ) (n : ℕ) :
    strictAdicAugmentationApp X I Kt (n + 1) ≫
        (strictAdicReductionTower X I Kt).map (homOfLE (Nat.le_succ n)).op =
      strictAdicAugmentationApp X I Kt n := by
  refine Eq.trans (congrArg (fun w => strictAdicAugmentationApp X I Kt (n + 1) ≫ w)
    (strictAdicReductionTower_map_succ X I Kt n)) ?_
  exact (Category.assoc _ _ _).trans (congrArg _
    (((Functor.map_comp _ _ _).symm).trans (congrArg _ (strictAdicQuotientπ_comp_map X I n))))

/-- **The strict cone on the strictified adic quotient tower, with vertex `K̃`.** This is the
cone of [Stacks, Tag 0CQH], taken out of `K̃` — a model of `K` — and *not* out of the derived
completion of `K`. -/
def strictAdicAugmentation (Kt : CochainComplex (Modules X) ℤ) :
    Stacks.MilnorTower.TowerAugmentation (strictAdicReductionTower X I Kt) where
  source := Kt
  app n := strictAdicAugmentationApp X I Kt n
  naturality n := strictAdicAugmentationApp_naturality X I Kt n

/-- The vertex of the strict cone is `K̃`. -/
@[simp]
theorem strictAdicAugmentation_source (Kt : CochainComplex (Modules X) ℤ) :
    (strictAdicAugmentation X I Kt).source = Kt :=
  rfl

/-- The `n`-th map of the strict cone is
`AlgebraicGeometry.RingedSite.strictAdicAugmentationApp`. -/
@[simp]
theorem strictAdicAugmentation_app (Kt : CochainComplex (Modules X) ℤ) (n : ℕ) :
    (strictAdicAugmentation X I Kt).app n = strictAdicAugmentationApp X I Kt n :=
  rfl

/-! ### The image of the strict cone is the cone of derived reductions -/

/-- **The image in `D(𝒪)` of the `n`-th map of the strict cone is the derived reduction**
`Q K̃ ⟶ Q K̃ ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, formed with the derived tensor product `T`, read through the
K-flat comparison. -/
theorem Q_strictAdicAugmentationApp (T : Stacks.SheafOfModules.DerivedTensorProduct X)
    (Kt : CochainComplex (Modules X) ℤ) (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) (n : ℕ) :
    ((T.unitIso (DerivedCategory.Q.obj Kt)).inv ≫
          (T.tensor.obj (DerivedCategory.Q.obj Kt)).map
            (DerivedCategory.Q.map (strictAdicQuotientπ X I n))) ≫
        (T.comparisonLeft Kt (strictAdicQuotientObj X I n) hKt).hom =
      DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n) := by
  have hU : Stacks.SheafOfModules.IsKFlat X.O (Stacks.SheafOfModules.unitCochainComplex X) :=
    Stacks.SheafOfModules.isKFlat_single_unit X.O
  have hLR : (T.comparisonLeft Kt (Stacks.SheafOfModules.unitCochainComplex X) hKt).hom =
      (T.comparisonRight Kt (Stacks.SheafOfModules.unitCochainComplex X) hU).hom :=
    congrArg Iso.hom
      ((T.comparisonLeft_eq_comparison Kt _ hKt hU).trans
        (T.comparisonRight_eq_comparison Kt _ hKt hU).symm)
  have hunit : (T.unitIso (DerivedCategory.Q.obj Kt)).inv ≫
      (T.comparisonLeft Kt (Stacks.SheafOfModules.unitCochainComplex X) hKt).hom =
      DerivedCategory.Q.map
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv := by
    rw [hLR, show (T.comparisonRight Kt (Stacks.SheafOfModules.unitCochainComplex X) hU).hom =
        (T.unitIso (DerivedCategory.Q.obj Kt)).hom ≫ DerivedCategory.Q.map
          (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv from by
        rw [T.unitIso_hom_q X Kt, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id],
      Iso.inv_hom_id_assoc]
  rw [Category.assoc, ← Q_map_tensorComplex_map X T Kt hKt (strictAdicQuotientπ X I n),
    ← Category.assoc, hunit, ← DerivedCategory.Q.map_comp]
  rfl

/-- **The image in `D(𝒪)` of the `n`-th map of the strict cone is the derived reduction**
`Q K̃ ⟶ Q K̃ ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of `AlgebraicGeometry.RingedSite.adicQuotientReduction`, read
through the K-flat comparison. This is `AlgebraicGeometry.RingedSite.Q_strictAdicAugmentationApp`
at the canonical derived tensor product of [Stacks, Tag 06YU]. -/
theorem adicQuotientReduction_comp_comparisonLeft (Kt : CochainComplex (Modules X) ℤ)
    (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) (n : ℕ) :
    adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft Kt
          (strictAdicQuotientObj X I n) hKt).hom =
      DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n) :=
  Q_strictAdicAugmentationApp X I (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
    Kt hKt n

end AlgebraicGeometry.RingedSite

end

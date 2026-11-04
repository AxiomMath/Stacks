module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualProIsoKoszul
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualProIsoStrictMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualOfKoszulComplex
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientKoszulLimit

/-!
# The dual Koszul tower is the tower of Koszul complexes in degrees `-r, …, 0`

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let
`K_n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`.
`AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso`
identifies the derived dual `K_n^∨` of [Stacks, Tag 08JD] with the image in `D(𝒪)` of the
explicit complex `AlgebraicGeometry.RingedSite.koszulPowerDualComplex`, the Koszul complex read
in degrees `-r, …, 0`. It is stated at one `n`. This file makes the family **natural in `n`**, so
that the tower `AlgebraicGeometry.RingedSite.koszulPowerDualSystem` of [Stacks, Tag 0A0E] — the
system the source of [Stacks, Tag 099M] calls `{K_n}` — is *isomorphic as a diagram* to the tower
of explicit complexes, hence pro-isomorphic to it.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDualKoszulPowerSystemIso`: **the isomorphism of
  `ℕᵒᵖ`-diagrams** between the dual Koszul tower and the tower of Koszul complexes in degrees
  `-r, …, 0` pushed into `D(𝒪)`.
* `AlgebraicGeometry.RingedSite.koszulPowerDualProIso`: the resulting pro-isomorphism of inverse
  systems.

## Main results

* `AlgebraicGeometry.RingedSite.dualComplexMap_comp_dualComplexKoszulPowerComplexIso`: the
  complex-level half — the identification of the dual complex of [Stacks, Tag 0FPR] of `K_n` with
  the Koszul complex in degrees `-r, …, 0` commutes with the transition maps.
* `AlgebraicGeometry.RingedSite.derivedDualMap_comp_derivedDualIsoQDualComplex`: **the
  identification of the derived dual with the image of the dual complex of [Stacks, Tag 0FPR] is
  natural in the complex.**
* `AlgebraicGeometry.RingedSite.derivedDualMap_comp_derivedDualKoszulPowerComplexIso`: the
  naturality square of the Koszul identification.

## Implementation notes

**The three ingredients.** The square for `derivedDualIsoQDualComplex` is
`AlgebraicGeometry.RingedSite.derivedDualMap_comp_derivedDualIsoLeftDual` — the naturality of the
second assertion of [Stacks, Tag 0FPV], whose right edge is the *mate* of the morphism for the
two pairings — followed by two computations of that mate:
`Stacks.SheafOfModules.DerivedMonoidal.mate_exactPairingQ` brings it back from `D(𝒪)` to the
category of complexes, and `Stacks.SheafOfModules.Strict.mate_exactPairingDualComplex` identifies
it there with `Stacks.SheafOfModules.Strict.dualComplexMap`. The Koszul square then adds
`CochainComplex.dualComplexMap_comp_dualComplexIso`, the naturality of the uniqueness
isomorphism of dual complexes.

**Why the two halves are in separate sections.** The complex-level statements are over the
strict monoidal structure of [Stacks, Tag 0FPQ] on `Mod(𝒪)` and the derived statements over the
re-seated one of [Stacks, Tag 0FPT]; `Mod(𝒪)` carries both, with the same tensor product, and a
single `MonoidalCategory (Mod 𝒪)` query cannot serve them both. The first section therefore has
no derived monoidal structure in scope, and the statement that crosses between them,
`derivedDualMap_comp_derivedDualIsoQDualComplex`, names the complex-level map as
`Stacks.SheafOfModules.Strict.dualComplexMap`, whose type mentions no monoidal structure at all.

**No tag.** [Stacks, Tag 0A0E] displays the tower `{K_n}` and identifies its terms; the
naturality of that identification is not a numbered statement, and neither is the pro-isomorphism
below — [Stacks, Tag 099M] needs the comparison with the adic quotients, which is
[Stacks, Tag 0921] and is not this.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section ComplexLevel

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The transition map of the tower of Koszul complexes in degrees `-r, …, 0`** induced by a
morphism of Koszul complexes: degreewise the mate of its components for the self-dualities of
the terms. The transition maps of `AlgebraicGeometry.RingedSite.koszulPowerDualComplexSystem` are
its values, and its type mentions no monoidal structure, so a consumer working over the derived
tensor product of [Stacks, Tag 0FPT] can name it. -/
def koszulPowerDualComplexMap (m n : ℕ)
    (φ : koszulPowerComplex X f m ⟶ koszulPowerComplex X f n) :
    koszulPowerDualComplex X f n ⟶ koszulPowerDualComplex X f m :=
  letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  CochainComplex.dualComplexMap (koszulPowerComplex X f m)
    (fun j => (koszulPowerComplex X f m).X (-j)) (exactPairingKoszulPowerComplexIn X f m)
    (koszulPowerComplex X f n) (fun j => (koszulPowerComplex X f n).X (-j))
    (exactPairingKoszulPowerComplexIn X f n) φ

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transition maps of the tower of Koszul complexes in degrees `-r, …, 0` are the values of
`AlgebraicGeometry.RingedSite.koszulPowerDualComplexMap`. -/
theorem koszulPowerDualComplexSystem_map_eq {a b : ℕᵒᵖ} (g : a ⟶ b) :
    (koszulPowerDualComplexSystem X f).map g =
      koszulPowerDualComplexMap X f b.unop a.unop ((koszulPowerSystem X f).map g.unop) :=
  rfl

/-- **The identification of the dual complex of [Stacks, Tag 0FPR] of the Koszul complex with the
Koszul complex in degrees `-r, …, 0` commutes with the induced maps.** This is
`CochainComplex.dualComplexMap_comp_dualComplexIso` — the naturality of the uniqueness
isomorphism of dual complexes — read at the two families of degreewise duals of the Koszul
complex: the dual sheaves of its terms, and the terms themselves. -/
theorem dualComplexMap_comp_dualComplexKoszulPowerComplexIso (m n : ℕ)
    (φ : koszulPowerComplex X f m ⟶ koszulPowerComplex X f n) :
    Stacks.SheafOfModules.Strict.dualComplexMap X.O (koszulPowerComplex X f m)
          (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f m)
          (koszulPowerComplex X f n)
          (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f n) φ ≫
        (dualComplexKoszulPowerComplexIso X f m
          (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f m)).hom =
      (dualComplexKoszulPowerComplexIso X f n
          (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f n)).hom ≫
        koszulPowerDualComplexMap X f m n φ := by
  let : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  let : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  exact CochainComplex.dualComplexMap_comp_dualComplexIso (koszulPowerComplex X f m) _ _
    (Stacks.SheafOfModules.Strict.dualComplexPairing X.O (koszulPowerComplex X f m)
      (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f m))
    (exactPairingKoszulPowerComplexIn X f m)
    (koszulPowerComplex X f n) _ _
    (Stacks.SheafOfModules.Strict.dualComplexPairing X.O (koszulPowerComplex X f n)
      (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f n))
    (exactPairingKoszulPowerComplexIn X f n) φ

end ComplexLevel

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The identification of the derived dual with the image of the dual complex of
[Stacks, Tag 0FPR] is natural in the complex.** For `φ : ℱ^• ⟶ ℱ'^•` the derived dual of `Q φ`
and the induced morphism `Stacks.SheafOfModules.Strict.dualComplexMap` of dual complexes are
carried to one another by `AlgebraicGeometry.RingedSite.derivedDualIsoQDualComplex`. -/
theorem derivedDualMap_comp_derivedDualIsoQDualComplex
    (F : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ)
    (hterm : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) (F.X n))
    (s : Finset ℤ) (hb : ∀ m, m ∉ s → IsZero (F.X m))
    (hFk : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O F)
    (hGk : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O
      (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm))
    (F' : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ)
    (hterm' : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) (F'.X n))
    (s' : Finset ℤ) (hb' : ∀ m, m ∉ s' → IsZero (F'.X m))
    (hFk' : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O F')
    (hGk' : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O
      (Stacks.SheafOfModules.Strict.dualComplex X.O F' hterm'))
    (φ : F ⟶ F') :
    derivedDualMap X (DerivedCategory.Q.map φ) ≫
        (derivedDualIsoQDualComplex X F hterm s hb hFk hGk).hom =
      (derivedDualIsoQDualComplex X F' hterm' s' hb' hFk' hGk').hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.Strict.dualComplexMap X.O F hterm F' hterm' φ) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ X.O F
    (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm) hFk hGk
    (Stacks.SheafOfModules.Strict.exactPairingDualComplex X.O F hterm s hb)
  let := Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ X.O F'
    (Stacks.SheafOfModules.Strict.dualComplex X.O F' hterm') hFk' hGk'
    (Stacks.SheafOfModules.Strict.exactPairingDualComplex X.O F' hterm' s' hb')
  have hA := derivedDualMap_comp_derivedDualIsoLeftDual X (DerivedCategory.Q.obj F)
    (DerivedCategory.Q.obj (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm))
    (DerivedCategory.Q.obj F')
    (DerivedCategory.Q.obj (Stacks.SheafOfModules.Strict.dualComplex X.O F' hterm'))
    (DerivedCategory.Q.map φ)
  have hB := Stacks.SheafOfModules.DerivedMonoidal.mate_exactPairingQ X.O F
    (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm) F'
    (Stacks.SheafOfModules.Strict.dualComplex X.O F' hterm') hFk hGk hFk' hGk'
    (Stacks.SheafOfModules.Strict.exactPairingDualComplex X.O F hterm s hb)
    (Stacks.SheafOfModules.Strict.exactPairingDualComplex X.O F' hterm' s' hb') φ
  have hC := Stacks.SheafOfModules.Strict.mate_exactPairingDualComplex X.O F hterm s hb F'
    hterm' s' hb' φ
  exact hA.trans ((derivedDualIsoQDualComplex X F' hterm' s' hb' hFk' hGk').hom ≫=
    hB.trans (congrArg DerivedCategory.Q.map hC))

/-- **The naturality square of the Koszul identification.** A morphism `K_m ⟶ K_n` of Koszul
complexes, its derived dual, and the induced map of the Koszul complexes in degrees `-r, …, 0`
form a commuting square with the two identifications
`AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso`. -/
theorem derivedDualMap_comp_derivedDualKoszulPowerComplexIso {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (m n : ℕ)
    (φ : koszulPowerComplex X f m ⟶ koszulPowerComplex X f n) :
    derivedDualMap X (DerivedCategory.Q.map φ) ≫
        (derivedDualKoszulPowerComplexIso X f m).hom =
      (derivedDualKoszulPowerComplexIso X f n).hom ≫
        DerivedCategory.Q.map (koszulPowerDualComplexMap X f m n φ) := by
  have hstep := derivedDualMap_comp_derivedDualIsoQDualComplex X _
    (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f m)
    (Finset.Icc (0 : ℤ) (r : ℤ)) (isZero_koszulPowerComplex_X_of_not_mem_Icc X f m)
    (kFlatComplexes_of_isStrictlyPerfect X _ (isStrictlyPerfect_koszulPowerComplex X f m))
    (kFlatComplexes_dualComplex X _ _ (isStrictlyPerfect_koszulPowerComplex X f m)) _
    (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f n)
    (Finset.Icc (0 : ℤ) (r : ℤ)) (isZero_koszulPowerComplex_X_of_not_mem_Icc X f n)
    (kFlatComplexes_of_isStrictlyPerfect X _ (isStrictlyPerfect_koszulPowerComplex X f n))
    (kFlatComplexes_dualComplex X _ _ (isStrictlyPerfect_koszulPowerComplex X f n)) φ
  have hiso := dualComplexMap_comp_dualComplexKoszulPowerComplexIso X f m n φ
  show derivedDualMap X (DerivedCategory.Q.map φ) ≫
      (derivedDualIsoQDualComplex X (koszulPowerComplex X f m) _ _ _ _ _).hom ≫
        DerivedCategory.Q.map (dualComplexKoszulPowerComplexIso X f m _).hom =
    ((derivedDualIsoQDualComplex X (koszulPowerComplex X f n) _ _ _ _ _).hom ≫
        DerivedCategory.Q.map (dualComplexKoszulPowerComplexIso X f n _).hom) ≫
      DerivedCategory.Q.map (koszulPowerDualComplexMap X f m n φ)
  rw [reassoc_of% hstep, Category.assoc, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp, hiso]

/-- **The dual Koszul tower is the tower of Koszul complexes in degrees `-r, …, 0`.** The
isomorphism of `ℕᵒᵖ`-diagrams whose component at `n` is
`AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso`: the derived dual
`K_n^∨ = R𝑆heafHom_𝒪(K(𝒪, f^{n+1}), 𝒪)` is the image in `D(𝒪)` of the explicit complex
`AlgebraicGeometry.RingedSite.koszulPowerDualComplex`, naturally in `n`. -/
def derivedDualKoszulPowerSystemIso {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    koszulPowerDualSystem X f ≅ koszulPowerDualComplexSystem X f ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun n => derivedDualKoszulPowerComplexIso X f n.unop)
    (fun {a b} g => derivedDualMap_comp_derivedDualKoszulPowerComplexIso X f b.unop a.unop
      ((koszulPowerSystem X f).map g.unop))

/-- **The dual Koszul tower is pro-isomorphic to the tower of Koszul complexes in degrees
`-r, …, 0`.** An isomorphism of `ℕᵒᵖ`-diagrams is a pro-isomorphism, by
`InverseSequence.ProIso.ofNatIso`. -/
def koszulPowerDualProIso {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    InverseSequence.ProIso (koszulPowerDualSystem X f)
      (koszulPowerDualComplexSystem X f ⋙ DerivedCategory.Q) :=
  InverseSequence.ProIso.ofNatIso (derivedDualKoszulPowerSystemIso X f)

end Derived

end AlgebraicGeometry.RingedSite

end

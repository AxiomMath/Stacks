module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeTranspose
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonComposition

/-!
# The transpose of a pullback map on derived sections along a base change square

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces, and suppose given functors `S_X, S_{X'}, S_S, S_{S'}`
("derived sections") from the four derived categories to two categories related by an adjunction
`ext ⊣ res`, together with Leray isomorphisms `res ∘ S_{X'} ≅ S_X ∘ Rg'_*`,
`res ∘ S_{S'} ≅ S_S ∘ Rg_*`, `S_X ≅ S_S ∘ Rf_*` and `S_{X'} ≅ S_{S'} ∘ Rf'_*` that are compatible
around the square. Then the transpose under `ext ⊣ res` of the pullback map
`S_X(F) ⟶ res S_{X'}(Lg'^* F)` is an isomorphism as soon as the derived base change map
`Lg^* Rf_* F ⟶ Rf'_* Lg'^* F` of [Stacks, Tag 08HY] and the transpose of the pullback map
`S_S(Rf_* F) ⟶ res S_{S'}(Lg^* Rf_* F)` are.

This is the formal half of flat base change for derived global sections over an affine base,
`AlgebraicGeometry.LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap`, where the
sections functors are `A`- and `B`-linear derived global sections and `ext ⊣ res` is derived
extension and restriction of scalars.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_homEquiv_symm_of_baseChange`: the statement over
  abstract adjunctions in the `Mate` form of `BaseChangeTranspose.lean`.
* `Stacks.Cohomology.DerivedBaseChange.isIso_homEquiv_symm_of_baseChange_canonical`: the statement
  at the canonical derived adjunctions of a commutative square of ringed spaces, with the
  comparison of the two iterated derived direct images written through the composition
  isomorphisms of [Stacks, Tag 079W].

## Implementation notes

As in `BaseChangeTranspose.lean`, the chase is done over variables, and the canonical statement is
written with the comparison of the iterated derived direct images unfolded exactly as
`derivedPushforwardComparisonSquare_app_eq_compIso` writes it, so that the kernel never has to
compare two spellings of the same derived-functor object.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- The bookkeeping of the transpose of a pullback map, in an arbitrary category. -/
theorem baseChange_transpose_chase {𝒞 : Type*} [Category 𝒞] {P P₁ Q R₀ R₁ R₂ R₃ R₄ R₅ : 𝒞}
    (ηg : P ⟶ P₁) (Λσ : Q ≅ P₁) (m₀ : P ⟶ R₀) (m₁ : P₁ ⟶ R₁) (c : R₀ ⟶ R₁) (k : R₁ ⟶ R₄)
    (ηb : R₀ ⟶ R₂) (Λτ₂ : R₃ ≅ R₂) (bcB : R₃ ⟶ R₅) (Rbbc : R₂ ⟶ R₄) (Λτ₄ : R₅ ≅ R₄)
    (ν : Q ⟶ R₅)
    (hnat₁ : ηg ≫ m₁ = m₀ ≫ c) (hM₁ : ηb ≫ Rbbc = c ≫ k)
    (hnatτ : bcB ≫ Λτ₄.hom = Λτ₂.hom ≫ Rbbc) (hM₃ : Λσ.hom ≫ m₁ ≫ k = ν ≫ Λτ₄.hom) :
    m₀ ≫ (ηb ≫ Λτ₂.inv) ≫ bcB = (ηg ≫ Λσ.inv) ≫ ν := by
  have h₁ : Λτ₂.inv ≫ bcB = Rbbc ≫ Λτ₄.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnatτ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₂ : ν = Λσ.hom ≫ m₁ ≫ k ≫ Λτ₄.inv := by
    rw [reassoc_of% hM₃, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc]
  rw [h₁, reassoc_of% hM₁, ← reassoc_of% hnat₁, h₂, Iso.inv_hom_id_assoc]

/-! ### The assembly, over abstract functors -/


/-- **The transpose of a pullback map along a base change square, over abstract functors.**
Let `Lg' ⊣ Rg'` and `Lg ⊣ Rg` be adjunctions (the two horizontal edges of a square), `Rf`, `Rf'`
functors (its vertical edges), `κ : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg` and `β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` related by
`hM₁` (the transpose identity of a base change map), and let "sections" functors
`Sf, Sf', SA, SB` to two categories with an adjunction `ext ⊣ res` carry Leray isomorphisms
`Λσ, Λτ, μ, μ'` compatible with `κ` (`happ`, `hM₃`). If `β` is invertible at `F` and the transpose
of the pullback map at `Rf F` is invertible, then so is the transpose of the pullback map at
`F`. -/
theorem isIso_homEquiv_symm_of_baseChange {DX DX' DS DS' MA MB : Type*} [Category DX]
    [Category DX'] [Category DS] [Category DS'] [Category MA] [Category MB]
    {Lg' : DX ⥤ DX'} {Rg' : DX' ⥤ DX} (adjg' : Lg' ⊣ Rg')
    {Lg : DS ⥤ DS'} {Rg : DS' ⥤ DS} (adjg : Lg ⊣ Rg) {Rf : DX ⥤ DS} {Rf' : DX' ⥤ DS'}
    (β : TwoSquare Rf Lg' Lg Rf')
    {ext : MA ⥤ MB} {res : MB ⥤ MA} (adjE : ext ⊣ res)
    {Sf : DX ⥤ MA} {Sf' : DX' ⥤ MB} {SA : DS ⥤ MA} {SB : DS' ⥤ MB}
    (Λσ : Sf' ⋙ res ≅ Rg' ⋙ Sf) (Λτ : SB ⋙ res ≅ Rg ⋙ SA)
    (μ : Sf ⟶ Rf ⋙ SA) [IsIso μ] (μ' : Sf' ⟶ Rf' ⋙ SB) [IsIso μ'] (F : DX)
    {Y₁ Y₂ : DS} (c₁ : (Rg' ⋙ Rf).obj (Lg'.obj F) ⟶ Y₁) (e : Y₁ ⟶ Y₂)
    (c₂ : Y₂ ⟶ (Rf' ⋙ Rg).obj (Lg'.obj F))
    (happ : (mateEquiv adjg' adjg β).app (Lg'.obj F) = c₁ ≫ e ≫ c₂)
    (hM₃ : Λσ.hom.app (Lg'.obj F) ≫ μ.app (Rg'.obj (Lg'.obj F)) ≫ SA.map c₁ ≫ SA.map e ≫
      SA.map c₂ = res.map (μ'.app (Lg'.obj F)) ≫ Λτ.hom.app (Rf'.obj (Lg'.obj F)))
    (hP₂ : IsIso ((adjE.homEquiv _ _).symm (SA.map (adjg.unit.app (Rf.obj F)) ≫
      Λτ.inv.app (Lg.obj (Rf.obj F)))))
    (hbc : IsIso (β.app F)) :
    IsIso ((adjE.homEquiv _ _).symm (Sf.map (adjg'.unit.app F) ≫ Λσ.inv.app (Lg'.obj F))) := by
  have hM₁ := unit_mateEquiv adjg' adjg β F
  rw [happ] at hM₁
  have hM₁' : SA.map (adjg.unit.app (Rf.obj F)) ≫ SA.map (Rg.map (β.app F)) =
      SA.map (Rf.map (adjg'.unit.app F)) ≫ (SA.map c₁ ≫ SA.map e ≫ SA.map c₂) := by
    simp only [← SA.map_comp, hM₁]
    rfl
  have hstar := baseChange_transpose_chase (Sf.map (adjg'.unit.app F)) (Λσ.app (Lg'.obj F))
    (μ.app F) (μ.app (Rg'.obj (Lg'.obj F))) (SA.map (Rf.map (adjg'.unit.app F)))
    (SA.map c₁ ≫ SA.map e ≫ SA.map c₂) (SA.map (adjg.unit.app (Rf.obj F)))
    (Λτ.app (Lg.obj (Rf.obj F))) (res.map (SB.map (β.app F))) (SA.map (Rg.map (β.app F)))
    (Λτ.app (Rf'.obj (Lg'.obj F))) (res.map (μ'.app (Lg'.obj F)))
    (μ.naturality _) hM₁' (Λτ.hom.naturality _) hM₃
  have key : (adjE.homEquiv _ _).symm (Sf.map (adjg'.unit.app F) ≫ Λσ.inv.app (Lg'.obj F)) ≫
      μ'.app (Lg'.obj F) = ext.map (μ.app F) ≫
        (adjE.homEquiv _ _).symm (SA.map (adjg.unit.app (Rf.obj F)) ≫
          Λτ.inv.app (Lg.obj (Rf.obj F))) ≫ SB.map (β.app F) := by
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm]
    congr 1
    simp only [Category.assoc] at hstar ⊢
    exact hstar.symm
  have : IsIso ((adjE.homEquiv _ _).symm (Sf.map (adjg'.unit.app F) ≫ Λσ.inv.app (Lg'.obj F)) ≫
      μ'.app (Lg'.obj F)) := by
    rw [key]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hP₂ inferInstance)
  exact IsIso.of_isIso_comp_right _ (μ'.app (Lg'.obj F))

section Canonical

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- **The comparison of the two iterated derived direct images, as the mate of the derived base
change square, is the pair of composition isomorphisms.** This is
`derivedPushforwardComparisonSquare_natTrans_eq_compIso` for the mate of
`derivedBaseChangeSquare g' f' f g sq` itself, the square in which [Stacks, Tag 08IB] is stated. -/
theorem mateEquiv_derivedBaseChangeSquare_natTrans_eq_compIso :
    (mateEquiv (derivedAdjunction g') (derivedAdjunction g)
        (derivedBaseChangeSquare g' f' f g sq)).natTrans =
      (derivedPushforwardCompIso g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ S => derivedPushforward k) sq) ≫
          (derivedPushforwardCompIso f' g).inv :=
  (Mate.derivedPushforwardComparisonSquare_eq_conjugateEquiv_comp (derivedAdjunction f)
      (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
      (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f)
      (derivedAdjunction (g' ≫ f))).trans
    ((congrArg (· ≫ _)
        (DerivedPushforwardAssociativity.conjugateEquiv_derivedPullbackCompIsoCanonical_inv
          g' f)).trans
      (congrArg (_ ≫ ·) (conjugateEquiv_derivedPullbackCompIsoLeft_hom g' f' f g sq)))

/-- `mateEquiv_derivedBaseChangeSquare_natTrans_eq_compIso` at an object. -/
theorem mateEquiv_derivedBaseChangeSquare_app_eq_compIso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    (mateEquiv (derivedAdjunction g') (derivedAdjunction g)
        (derivedBaseChangeSquare g' f' f g sq)).app M =
      (derivedPushforwardCompIso g' f).hom.app M ≫
        eqToHom (congrArg (fun k : X' ⟶ S => (derivedPushforward k).obj M) sq) ≫
          (derivedPushforwardCompIso f' g).inv.app M := by
  have h := congr_app (mateEquiv_derivedBaseChangeSquare_natTrans_eq_compIso g' f' f g sq) M
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app] at h
  exact h

/-- `isIso_homEquiv_symm_of_baseChange` at the canonical derived adjunctions of a commutative
square of ringed spaces, with the comparison of the two iterated derived direct images written
through the composition isomorphisms. -/
theorem isIso_homEquiv_symm_of_baseChange_canonical
    {MA MB : Type*} [Category MA] [Category MB] {ext : MA ⥤ MB} {res : MB ⥤ MA}
    (adjE : ext ⊣ res)
    {Sf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤ MA}
    {Sf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤ MB}
    {SA : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤ MA}
    {SB : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤ MB}
    (Λσ : Sf' ⋙ res ≅ derivedPushforward g' ⋙ Sf) (Λτ : SB ⋙ res ≅ derivedPushforward g ⋙ SA)
    (μ : Sf ⟶ derivedPushforward f ⋙ SA) [IsIso μ]
    (μ' : Sf' ⟶ derivedPushforward f' ⋙ SB) [IsIso μ']
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hM₃ : Λσ.hom.app ((derivedPullback g').obj F) ≫
      μ.app ((derivedPushforward g').obj ((derivedPullback g').obj F)) ≫
      SA.map ((derivedPushforwardCompIso g' f).hom.app ((derivedPullback g').obj F)) ≫
      SA.map (eqToHom (congrArg (fun k : X' ⟶ S => (derivedPushforward k).obj
        ((derivedPullback g').obj F)) sq)) ≫
      SA.map ((derivedPushforwardCompIso f' g).inv.app ((derivedPullback g').obj F)) =
      res.map (μ'.app ((derivedPullback g').obj F)) ≫
        Λτ.hom.app ((derivedPushforward f').obj ((derivedPullback g').obj F)))
    (hP₂ : IsIso ((adjE.homEquiv _ _).symm (SA.map ((derivedAdjunction g).unit.app
      ((derivedPushforward f).obj F)) ≫
      Λτ.inv.app ((derivedPullback g).obj ((derivedPushforward f).obj F)))))
    (hbc : IsIso (derivedBaseChangeMap g' f' f g sq F)) :
    IsIso ((adjE.homEquiv _ _).symm (Sf.map ((derivedAdjunction g').unit.app F) ≫
      Λσ.inv.app ((derivedPullback g').obj F))) :=
  isIso_homEquiv_symm_of_baseChange (derivedAdjunction g') (derivedAdjunction g)
    (derivedBaseChangeSquare g' f' f g sq) adjE Λσ Λτ μ μ' F _ _ _
    (mateEquiv_derivedBaseChangeSquare_app_eq_compIso g' f' f g sq ((derivedPullback g').obj F))
    hM₃ hP₂ hbc

end Canonical

end Stacks.Cohomology.DerivedBaseChange

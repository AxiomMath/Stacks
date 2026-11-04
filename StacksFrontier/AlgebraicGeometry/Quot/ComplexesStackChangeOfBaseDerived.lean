module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackChangeOfBaseSpaces
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSmallerBaseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectSmallerBase
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent

/-!
# The change of base scheme for `Complexes`, the derived categories

For a matched pair `A`, `A₁` of test schemes of
`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum` (over the final `D.Y` and over
`D₁.Y`), the identification `Λ_g X_A ≅ X₁_{A₁}` gives an equivalence
`D(𝒪_{X₁_{A₁}}) ≌ D(𝒪_{X_A})` (Stacks 04SG,
`AlgebraicGeometry.Space.smallerBaseDerivedEquivalence`). This file records what the comparison
of `Complexes_{X/T}` with `Complexes_{X₁/T}` needs of it:

* it commutes with derived pullback along compatible morphisms of base changes, compatibly with
  the composition comparisons of Stacks 0D6D
  (`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.pullbackIso_triangle`);
* the induced bijection on fibre morphisms
  (`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.transpose`);
* it preserves and reflects conditions (1) and (2) of Stacks 0DLD
  (`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.isRelativelyPerfect_iff`,
  `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.hasNoNegativeFibreExt_iff`).

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

/-- From `a ≫ x = y ≫ c` for isomorphisms `a` and `c`, `x ≫ c⁻¹ = a⁻¹ ≫ y`. -/
theorem _root_.CategoryTheory.Iso.comp_inv_eq_inv_comp_of_hom_comp_eq_comp_hom {𝒞 : Type*}
    [Category* 𝒞]
    {X Y Z W : 𝒞} (α : X ≅ Y) (x : Y ⟶ Z) (γ : W ≅ Z) (y : X ⟶ W)
    (h : α.hom ≫ x = y ≫ γ.hom) : x ≫ γ.inv = α.inv ≫ y := by
  rw [Iso.comp_inv_eq, Category.assoc, ← h, Iso.inv_hom_id_assoc]

/-! ### The comparison of derived pullbacks and the triangles of Stacks 0D6D -/

section Triangle

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Z₁ Z₂ Z₃ : AlgebraicSpaces B W hW}
  {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  (ε₃ : (OverShriek.relocalizePresheafFunctor h).obj Z₃.1 ≅ Y₃.1)
  {f : Z₁ ⟶ Z₂} {f' : Z₂ ⟶ Z₃} {f₃ : Z₁ ⟶ Z₃} {k : Y₁ ⟶ Y₂} {k' : Y₂ ⟶ Y₃} {k₃ : Y₁ ⟶ Y₃}
  (hfk : ε₁.hom ≫ k.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  (hf : yoneda.relativelyRepresentable f.hom) (hk : yoneda.relativelyRepresentable k.hom)
  (hfk' : ε₂.hom ≫ k'.hom = (OverShriek.relocalizePresheafFunctor h).map f'.hom ≫ ε₃.hom)
  (hf' : yoneda.relativelyRepresentable f'.hom) (hk' : yoneda.relativelyRepresentable k'.hom)
  (hfk₃ : ε₁.hom ≫ k₃.hom = (OverShriek.relocalizePresheafFunctor h).map f₃.hom ≫ ε₃.hom)
  (hf₃ : yoneda.relativelyRepresentable f₃.hom) (hk₃ : yoneda.relativelyRepresentable k₃.hom)

/-- **The comparison of derived pullbacks with the change of base is compatible with the
triangles of the derived pullback datum** (Stacks 0D6D): the form of
`AlgebraicGeometry.Space.smallerBaseDerivedPullbackIso_comp` for arbitrary composites
`f ≫ f' = f₃` and `k ≫ k' = k₃`. -/
theorem smallerBaseDerivedPullbackIso_triangle (hff : f ≫ f' = f₃) (hkk : k ≫ k' = k₃)
    (K : derivedModules B S hS Y₃) :
    (smallerBaseDerivedPullbackIso B h ε₁ ε₃ hfk₃ hf₃ hk₃).hom.app K ≫
        ((smallEtaleDerivedPullbackData B W hW).triangle hff).hom.app
          ((smallerBaseDerivedEquivalence B h ε₃).functor.obj K) =
      (smallerBaseDerivedEquivalence B h ε₁).functor.map
          (((smallEtaleDerivedPullbackData B S hS).triangle hkk).hom.app K) ≫
        (smallerBaseDerivedPullbackIso B h ε₁ ε₂ hfk hf hk).hom.app
          ((smallEtaleDerivedPullbackData B S hS).pull k' |>.obj K) ≫
        ((smallEtaleDerivedPullbackData B W hW).pull f).map
          ((smallerBaseDerivedPullbackIso B h ε₂ ε₃ hfk' hf' hk').hom.app K) := by
  subst hff hkk
  rw [PullbackData.triangle_eq, PullbackData.triangle_eq, eqToIso_refl, eqToIso_refl,
    Iso.refl_trans, Iso.refl_trans, smallEtaleDerivedPullbackData_compIso_eq,
    smallEtaleDerivedPullbackData_compIso_eq, Iso.symm_hom, Iso.symm_hom]
  exact Iso.comp_inv_eq_inv_comp_of_hom_comp_eq_comp_hom
    ((smallerBaseDerivedEquivalence B h ε₁).functor.mapIso
    ((smallEtaleDerivedModulePullbackCompIso B S hS k k').app K)) _
    ((smallEtaleDerivedModulePullbackCompIso B W hW f f').app
      ((smallerBaseDerivedEquivalence B h ε₃).functor.obj K)) _
    ((smallerBaseDerivedPullbackIso_comp B h ε₁ ε₂ ε₃ hfk hf hk hfk' hf' hk' hfk₃ hf₃ hk₃
      K).trans (Category.assoc _ _ _).symm)

end Triangle

/-! ### Shifted self-extensions along equivalences -/

section Shift

variable {𝒟 𝒟' : Type*} [Category* 𝒟] [Category* 𝒟'] [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ]

/-- Vanishing of the `i`-th self-extensions is invariant under isomorphism. -/
theorem subsingleton_shift_iff_of_iso {X Y : 𝒟} (e : X ≅ Y) (i : ℤ) :
    Subsingleton (X ⟶ X⟦i⟧) ↔ Subsingleton (Y ⟶ Y⟦i⟧) :=
  (Iso.homCongr e ((shiftFunctor 𝒟 i).mapIso e)).subsingleton_congr

/-- Vanishing of the `i`-th self-extensions is preserved and reflected by a fully faithful functor
commuting with the `i`-th shift. -/
theorem subsingleton_shift_iff_of_fullyFaithful (F : 𝒟 ⥤ 𝒟') (hF : F.FullyFaithful) (X : 𝒟)
    (i : ℤ) (e : F.obj (X⟦i⟧) ≅ (F.obj X)⟦i⟧) :
    Subsingleton (X ⟶ X⟦i⟧) ↔ Subsingleton (F.obj X ⟶ (F.obj X)⟦i⟧) :=
  (hF.homEquiv.trans (Iso.homCongr (Iso.refl _) e)).subsingleton_congr

end Shift

namespace ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChangeOfBaseDatum

variable {T : Scheme.{u}} {hT : B.Contains T} {g : B.obj hT ⟶ B.obj hS}
  {C : ChangeOfBaseDatum B hT hS g}

/-! ### The equivalence of derived categories along a match -/

/-- `D(𝒪_{X₁_{A₁}}) ≌ D(𝒪_{X_A})` along a match `m` (Stacks 04SG), written out where it is used:
`AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` at `Λ_g X_A ≅ X₁_{A₁}`. -/
local notation "𝔼[" m "]" => smallerBaseDerivedEquivalence B g (Match.spaceIso m)

/-- The equivalence of a match commutes with the shifts. -/
def Match.shiftIso {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y} (m : C.Match A A₁)
    (X : derivedModules B S hS (C.D₁.space A₁)) (i : ℤ) :
    𝔼[m].functor.obj (X⟦i⟧) ≅ (𝔼[m].functor.obj X)⟦i⟧ :=
  ((smallerBaseModulesEquivalenceOfIso B g m.spaceIso).functor.mapDerivedCategory.commShiftIso
    i).app X

/-- Compatibility of matches is preserved by composing the morphisms of test schemes. -/
theorem Match.Compatible.comp {A A' A'' : SchemesOver C.D.Y} {A₁ A₁' A₁'' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {m'' : C.Match A'' A₁''} {k : A ⟶ A'}
    {k₁ : A₁ ⟶ A₁'} {k' : A' ⟶ A''} {k₁' : A₁' ⟶ A₁''} (hk : m.Compatible m' k k₁)
    (hk' : m'.Compatible m'' k' k₁') : m.Compatible m'' (k ≫ k') (k₁ ≫ k₁') := by
  change m.β.hom ≫ k₁.left ≫ k₁'.left = (Over.map g).map (k.left ≫ k'.left) ≫ m''.β.hom
  rw [← Category.assoc, hk, Category.assoc, hk', CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The equivalences of a match commute with derived pullback** along compatible morphisms of
test schemes. -/
abbrev Match.pullbackIso {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) :
    (smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁) ⋙ 𝔼[m].functor ≅
      𝔼[m'].functor ⋙ (smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k) :=
  smallerBaseDerivedPullbackIso B g m.spaceIso m'.spaceIso (Match.spaceIso_hom_relativeMap hk)
    (SpecLimitTower.relativelyRepresentable_relativeMap k)
    (SpecLimitTower.relativelyRepresentable_relativeMap k₁)

/-- **The comparison of derived pullbacks is compatible with the composition comparisons** of
`Complexes` over the two bases. -/
theorem Match.pullbackIso_triangle {A A' A'' : SchemesOver C.D.Y}
    {A₁ A₁' A₁'' : SchemesOver C.D₁.Y} {m : C.Match A A₁} {m' : C.Match A' A₁'}
    {m'' : C.Match A'' A₁''} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'} {k' : A' ⟶ A''} {k₁' : A₁' ⟶ A₁''}
    (hk : m.Compatible m' k k₁) (hk' : m'.Compatible m'' k' k₁')
    (hk'' : m.Compatible m'' (k ≫ k') (k₁ ≫ k₁')) (K : derivedModules B S hS (C.D₁.space A₁'')) :
    (Match.pullbackIso hk'').hom.app K ≫
        (C.D.compComparison k k').hom.app (𝔼[m''].functor.obj K) =
      𝔼[m].functor.map ((C.D₁.compComparison k₁ k₁').hom.app K) ≫
        (Match.pullbackIso hk).hom.app
          (((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁')).obj K) ≫
        ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).map
          ((Match.pullbackIso hk').hom.app K) := by
  have e : C.D.compComparison k k' =
      (smallEtaleDerivedPullbackData B T hT).triangle (f := C.D.relativeMap k)
        (g := C.D.relativeMap k') (k := C.D.relativeMap (k ≫ k'))
        (baseChangeMap_comp C.D.f k k').symm := rfl
  have e₁ : C.D₁.compComparison k₁ k₁' =
      (smallEtaleDerivedPullbackData B S hS).triangle (f := C.D₁.relativeMap k₁)
        (g := C.D₁.relativeMap k₁') (k := C.D₁.relativeMap (k₁ ≫ k₁'))
        (baseChangeMap_comp C.D₁.f k₁ k₁').symm := rfl
  rw [e, e₁]
  exact smallerBaseDerivedPullbackIso_triangle B g m.spaceIso m'.spaceIso m''.spaceIso
    (f := C.D.relativeMap k) (f' := C.D.relativeMap k') (f₃ := C.D.relativeMap (k ≫ k'))
    (k := C.D₁.relativeMap k₁) (k' := C.D₁.relativeMap k₁') (k₃ := C.D₁.relativeMap (k₁ ≫ k₁'))
    (Match.spaceIso_hom_relativeMap hk) (SpecLimitTower.relativelyRepresentable_relativeMap k)
    (SpecLimitTower.relativelyRepresentable_relativeMap k₁)
    (Match.spaceIso_hom_relativeMap hk') (SpecLimitTower.relativelyRepresentable_relativeMap k')
    (SpecLimitTower.relativelyRepresentable_relativeMap k₁')
    (Match.spaceIso_hom_relativeMap hk'')
    (SpecLimitTower.relativelyRepresentable_relativeMap (k ≫ k'))
    (SpecLimitTower.relativelyRepresentable_relativeMap (k₁ ≫ k₁'))
    (baseChangeMap_comp C.D.f k k').symm (baseChangeMap_comp C.D₁.f k₁ k₁').symm K

/-! ### Fibre morphisms -/

/-- **The bijection on fibre morphisms along a match**: a morphism `L(X_k)^* (F K') ⟶ E` over
`T` corresponds to a morphism `L(X₁_{k₁})^* K' ⟶ G E` over `S`, where `F` is the equivalence of
the target match and `G` the inverse of the equivalence of the source match. -/
def Match.transpose {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A)) :
    (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ⟶ E) ≃
      (((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁)).obj K' ⟶
        𝔼[m].inverse.obj E) :=
  (Iso.homCongr ((Match.pullbackIso hk).app K').symm (Iso.refl E)).trans
    (𝔼[m].toAdjunction.homEquiv _ _)

/-- Applying the equivalence of the source match to `Match.transpose hk K' E φ` and then the
counit recovers `φ`, precomposed with the comparison of derived pullbacks. -/
theorem Match.transpose_spec {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ⟶ E) :
    𝔼[m].functor.map (Match.transpose hk K' E φ) ≫ 𝔼[m].counit.app E =
      (Match.pullbackIso hk).hom.app K' ≫ φ := by
  have h := 𝔼[m].toAdjunction.homEquiv_counit
    (X := ((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁)).obj K') (Y := E)
    (Match.transpose hk K' E φ)
  rw [Equivalence.toAdjunction_counit] at h
  rw [← h]
  simp [Match.transpose, Iso.homCongr_apply]

/-- `Match.transpose` written out through the unit of the equivalence of the source match. -/
theorem Match.transpose_eq {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ⟶ E) :
    Match.transpose hk K' E φ = 𝔼[m].unitIso.hom.app _ ≫
      𝔼[m].inverse.map ((Match.pullbackIso hk).hom.app K' ≫ φ) := by
  simp [Match.transpose, Adjunction.homEquiv_unit, Iso.homCongr_apply]

/-- The bijection on fibre morphisms along a match sends isomorphisms to isomorphisms. -/
theorem Match.isIso_transpose {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ⟶ E) (hφ : IsIso φ) :
    IsIso (Match.transpose hk K' E φ) := by
  rw [Match.transpose_eq]
  exact IsIso.comp_isIso

/-- The bijection on fibre morphisms, on isomorphisms. -/
def Match.transposeIso {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (e : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ≅ E) :
    ((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁)).obj K' ≅
      𝔼[m].inverse.obj E :=
  𝔼[m].unitIso.app _ ≪≫
    𝔼[m].inverse.mapIso
      ((Match.pullbackIso hk).app K' ≪≫ e)

/-- The forward map of `Match.transposeIso` is `Match.transpose` of the forward map. -/
theorem Match.transposeIso_hom {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (e : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ≅ E) :
    (Match.transposeIso hk K' E e).hom = Match.transpose hk K' E e.hom := by
  rw [Match.transpose_eq]
  rfl

/-- The inverse of the bijection on fibre morphisms, on isomorphisms. -/
def Match.transposeSymmIso {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁)).obj K' ≅
      𝔼[m].inverse.obj E) :
    ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ≅ E :=
  ((Match.pullbackIso hk).app K').symm ≪≫
    𝔼[m].functor.mapIso e ≪≫
    𝔼[m].counitIso.app E

/-- `Match.transposeIso` undoes `Match.transposeSymmIso`, on forward maps. -/
theorem Match.transposeIso_transposeSymmIso_hom {A A' : SchemesOver C.D.Y}
    {A₁ A₁' : SchemesOver C.D₁.Y} {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'}
    {k₁ : A₁ ⟶ A₁'} (hk : m.Compatible m' k k₁) (K' : derivedModules B S hS (C.D₁.space A₁'))
    (E : derivedModules B T hT (C.D.space A))
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap k₁)).obj K' ≅
      𝔼[m].inverse.obj E) :
    (Match.transposeIso hk K' E (Match.transposeSymmIso hk K' E e)).hom = e.hom := by
  rw [Match.transposeIso_hom, show (Match.transposeSymmIso hk K' E e).hom =
      (Match.transpose hk K' E).symm e.hom by
    simp [Match.transposeSymmIso, Match.transpose, Iso.homCongr, Adjunction.homEquiv_counit],
    Equiv.apply_symm_apply]

/-- The bijection on fibre isomorphisms does not see which of two equal morphisms of test schemes
over `D₁.Y` it is formed along. -/
theorem Match.transposeIso_hom_heq {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ k₁' : A₁ ⟶ A₁'} (hb : k₁ = k₁')
    (hk : m.Compatible m' k k₁) (hk' : m.Compatible m' k k₁')
    (K' : derivedModules B S hS (C.D₁.space A₁')) (E : derivedModules B T hT (C.D.space A))
    (e : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj
        (𝔼[m'].functor.obj K') ≅ E) :
    HEq (Match.transposeIso hk K' E e).hom (Match.transposeIso hk' K' E e).hom := by
  subst hb
  rfl

/-! ### Conditions (1) and (2) of Stacks 0DLD -/

/-- **Condition (1) of Stacks 0DLD is preserved and reflected along a match**: Stacks 0DKN over
the two bases. -/
theorem Match.isRelativelyPerfect_iff {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) (K : derivedModules B S hS (C.D₁.space A₁)) :
    C.D₁.IsRelativelyPerfect A₁ K ↔ C.D.IsRelativelyPerfect A (𝔼[m].functor.obj K) :=
  smallerBaseRelativelyPerfectComparison B g m.spaceIso m.testIso
    (Match.spaceIso_hom_projection m) _ _ _ _ K

/-- **Condition (2) of Stacks 0DLD is preserved and reflected along a match.** A field-valued test
scheme over either base is matched with one over the other, and the derived pullbacks to it
correspond under the equivalences, which commute with the shifts. -/
theorem Match.hasNoNegativeFibreExt_iff {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) (K : derivedModules B S hS (C.D₁.space A₁)) :
    C.D₁.HasNoNegativeFibreExt A₁ K ↔
      C.D.HasNoNegativeFibreExt A (𝔼[m].functor.obj K) := by
  refine ⟨fun h T₀ hT₀ y i hi => ?_, fun h T₁ hT₁ y₁ i hi => ?_⟩
  · let m₀ := Match.refl C T₀
    exact (subsingleton_shift_iff_of_iso
      ((Match.pullbackIso (m₀.compatible_homOfSource m y)).app K) i).1
      ((subsingleton_shift_iff_of_fullyFaithful 𝔼[m₀].functor
        𝔼[m₀].fullyFaithfulFunctor _ i (m₀.shiftIso _ i)).1 (h (C.testScheme T₀) hT₀ _ i hi))
  · let m₀ := Match.ofTarget C T₁
    exact (subsingleton_shift_iff_of_fullyFaithful 𝔼[m₀].functor
      𝔼[m₀].fullyFaithfulFunctor _ i (m₀.shiftIso _ i)).2
      ((subsingleton_shift_iff_of_iso
        ((Match.pullbackIso (m₀.compatible_homOfTarget m y₁)).app K) i).2
        (h (C.ofTarget T₁) hT₁ _ i hi))

end ChangeOfBaseDatum

end ComplexesSituation

end AlgebraicGeometry.Space

end

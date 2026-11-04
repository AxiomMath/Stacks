module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCoreCoherent
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCoreCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingColimit
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# Stacks 0G2H and 0G4K

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `(K_n)` be a Deligne system
with value `K` on `U`. [Stacks, Tag 0G2H] asserts that the canonical restriction map

`colim_n Hom_X(K_n, L) ⟶ Hom_U(K, L|_U)`

is bijective for every `L` in `D^b_{Coh}(𝒪_X)`.
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` proves this from one
hypothesis, `hcore`: the identification for a one-degree truncation of the system against a
target concentrated in a single degree. **This file discharges `hcore`**, and with it the tag.

Through `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree`, `hcore`
for the pair of degrees `(p, q)` is the bijectivity of

`colim_n Ext^i_X(𝓘^n 𝓗, 𝓑) ⟶ Ext^i_U(𝓗|_U, 𝓑|_U)`, where `q + i = p`,

for `𝓗 = H^p(𝓕^•)` and `𝓑` coherent — the core case of the tag, and the third step of the
source's proof. Its two halves are now both proved in every degree:
`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent` for surjectivity and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent`
for injectivity, which are exactly the two hypotheses of
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem`. So the degrees `q < p`,
the only ones the source's induction on `i` is needed for, are discharged here, and the
degrees `p ≤ q` were already discharged by
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`.

## Stacks 0G4K: bounded-below targets

[Stacks, Tag 0G4K] says that the identification of 0G2H holds even for `L` in
`D^+_{Coh}(𝒪_X)`. The source's proof is followed: the terms of a Deligne system lie in degrees
`≤ b` for one `b` (`AlgebraicGeometry.DeligneSystem.exists_isGE_isLE_system`), so
`Hom_X(K_n, L) = Hom_X(K_n, τ^{≤b}L)` and `Hom_U(K, L|_U) = Hom_U(K, (τ^{≤b}L)|_U)`, and
`τ^{≤b}L` lies in `D^b_{Coh}(𝒪_X)`, where 0G2H applies. The first identification is Mathlib's
`CategoryTheory.Triangulated.TStructure.liftTruncLE`; the second, on `U`, is
`CategoryTheory.Triangulated.TStructure.bijective_comp_mor₁_of_isLE_of_isGE` for the restriction
of the truncation triangle `τ^{≤b}L ⟶ L ⟶ τ^{>b}L ⟶`, restriction to `U` being exact. Since `L`
is not an object of `D^b_{Coh}(𝒪_X)`, the statement is made in `D(𝒪_X)`: the cocone of
`CategoryTheory.restrictionHomCocone`, sending `g : K_n ⟶ L` to `K ≅ K_n|_U ⟶ L|_U`, is a colimit
cocone.

## Main results

* `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`: **`hcore`, unconditionally.**
* `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`: **[Stacks, Tag 0G2H].**
* `AlgebraicGeometry.DeligneSystem.restrictionLifting`: [Stacks, Tag 0G2H] in its elementwise
  form.
* `AlgebraicGeometry.DeligneSystem.restrictionLifting_of_derivedCategoryBPlus`: the elementwise
  form for a target in `D^+_{Coh}(𝒪_X)`.
* `AlgebraicGeometry.DeligneSystem.nonempty_isColimit_restrictionHomCocone`:
  **[Stacks, Tag 0G4K].**
* `AlgebraicGeometry.DeligneSystem.exists_comp_restrict_eq`: the surjectivity half of the tag,
  read as an extension property for a single morphism.

## Implementation notes

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance of raised priority,
as in `StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/CoherentExtEffacement.lean`:
the import closure of the coherent effacement carries locally small models at universe `u` as
global instances, and with those in scope the shift functors of `D^b_{Coh}(𝒪_X)` are no longer
found to be additive.

The hypotheses of `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` are
supplied at the point of use rather than packaged into a lemma of their own: that lemma's
`CategoryTheory.RestrictionLifting` is elaborated with the `Hom`-universe of the derived category
left to the elaborator, and stating it in isolation fixes it one level too high for the `hext`
hypothesis of
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree` to accept.
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le` supplies its degree-zero
hypothesis in the same way, for the same reason.

The two private lemmas `isLE_mapDerivedCategory_obj` and `isGE_mapDerivedCategory_obj` (an exact
functor preserves the bounds of an object of the derived category) restate
`Dualizing.mapDerivedCategory_isLE` and `Dualizing.mapDerivedCategory_isGE` of
`StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness`, whose import closure lies far outside
this file's. Both are one-line consequences of
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which is where the public statement
belongs once one is moved there.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4K](https://stacks.math.columbia.edu/tag/0G4K)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated
open Opposite

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.HasExt.standard

universe v u u₁ u₂ v₁ v₂ w₁ w₂

namespace CategoryTheory

namespace Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Morphisms out of `D^{≤b}` into the first vertex of a triangle whose third vertex is in
`D^{≥b+1}`.** For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` with `T₃` in `D^{≥b+1}` and an
object `Y` in `D^{≤b}`, composition with `T₁ ⟶ T₂` is a bijection
`Hom(Y, T₁) ⟶ Hom(Y, T₂)`: both `Hom(Y, T₃)` and `Hom(Y, T₃⟦-1⟧)` vanish. For the truncation
triangle of `T₂` this is the familiar `Hom(Y, τ^{≤b}T₂) = Hom(Y, T₂)`; the statement for an
arbitrary triangle is what applies after an exact functor. -/
public lemma bijective_comp_mor₁_of_isLE_of_isGE (t : TStructure C) (T : Triangle C)
    (hT : T ∈ distTriang C) (b : ℤ) [t.IsGE T.obj₃ (b + 1)] (Y : C) [t.IsLE Y b] :
    Function.Bijective fun g : Y ⟶ T.obj₁ => g ≫ T.mor₁ := by
  constructor
  · intro g₁ g₂ hg
    change g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ at hg
    rw [← sub_eq_zero]
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang _ hT)
      (g₁ - g₂) (by
        show (g₁ - g₂) ≫ T.mor₁ = 0
        rw [Preadditive.sub_comp, hg, sub_self])
    have : t.IsGE T.invRotate.obj₁ (b + 2) := t.isGE_shift T.obj₃ (b + 1) (-1) (b + 2)
    rw [hh, t.zero h b (b + 2)]
    exact zero_comp
  · intro g
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ T hT g (t.zero _ b (b + 1))
    exact ⟨g', hg'.symm⟩

end Triangulated.TStructure

/-- An exact functor preserves the upper bound of an object of the derived category: its
cohomology sheaves are those of the object, carried by the functor. -/
private lemma isLE_mapDerivedCategory_obj {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₁} C₁]
    [HasDerivedCategory.{w₂} C₂] (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory C₁) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE K n i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app K)

/-- An exact functor preserves the lower bound of an object of the derived category. -/
private lemma isGE_mapDerivedCategory_obj {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₁} C₁]
    [HasDerivedCategory.{w₂} C₂] (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory C₁) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isGE K n i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app K)

end CategoryTheory

namespace AlgebraicGeometry.DeligneSystem

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]
  (D : DeligneSystem j)

/-- **[Stacks, Tag 0G2H] in its elementwise form.** Restriction to `U` identifies
`colim_n Hom_X(K_n, L)` with `colim_n Hom_U(K_n|_U, L|_U)` elementwise, for every `L` in
`D^b_{Coh}(𝒪_X)`: every morphism `K_n|_U ⟶ L|_U` is, past some index, the restriction of a
morphism `K_m ⟶ L`, and two morphisms `K_n ⟶ L` with the same restriction agree past some index.

This is the two dévissages `CategoryTheory.restrictionLifting_of_core` applied to the core case
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`, over the degree range of
`AlgebraicGeometry.DeligneSystem.exists_isGE_isLE_system`. -/
public lemma restrictionLifting (L : BoundedCoherentDerived X) :
    RestrictionLifting D.system (restrictBoundedCoherent j) L := by
  obtain ⟨a, b, hab, hGE, hLE⟩ := D.exists_isGE_isLE_system
  exact CategoryTheory.restrictionLifting_of_core (restrictBoundedCoherent j)
    (boundedCoherentTStructure X) hab D.system hGE hLE
    exists_isGE_isLE_boundedCoherentTStructure
    (fun p q _ _ L hq hq' => D.restrictionLifting_truncGELE p q L hq hq') L

omit [IsNoetherian X] in
/-- **The truncation `τ^{≤b}L` of an object `L` of `D^+_{Coh}(𝒪_X)` lies in `D^b_{Coh}(𝒪_X)`.**
It is bounded above by `b`; below `b + 1` its cohomology sheaves are those of `L`, so it inherits
the lower bound of `L`; and each of its cohomology sheaves is either one of `L` or zero, hence
coherent. -/
public lemma _root_.AlgebraicGeometry.boundedCoherentDerived_truncLE_obj (b : ℤ)
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) L) :
    boundedCoherentDerived X ((DerivedCategory.TStructure.t.truncLE b).obj L) := by
  obtain ⟨⟨n₀, hn₀⟩, hcoh⟩ := hL
  refine ⟨⟨⟨n₀, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, ?_⟩
  · by_cases hib : i < b + 1
    · exact (hn₀ i hi).of_iso
        ((DerivedCategory.truncLTCompHomologyFunctorIso (b + 1) i hib).app L)
    · exact DerivedCategory.isZero_of_isLE ((DerivedCategory.TStructure.t.truncLE b).obj L) b i
        (by omega)
  · exact DerivedCategory.isZero_of_isLE ((DerivedCategory.TStructure.t.truncLE b).obj L) b i hi
  · exact DerivedCategoryB.derivedCategoryB_truncLT_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass (fun M : X.Modules => M.IsCoherent)) (b + 1) L
      hcoh

/-- **[Stacks, Tag 0G4K] in its elementwise form.** For `L` in `D^+_{Coh}(𝒪_X)` — an object of
`D(𝒪_X)` that is cohomologically bounded below with coherent cohomology sheaves — restriction to
`U` identifies `colim_n Hom_X(K_n, L)` with `colim_n Hom_U(K_n|_U, L|_U)` elementwise.

This is the source's argument. The terms of `(K_n)` lie in degrees `≤ b` for one `b`, so every
morphism `K_n ⟶ L` factors through `τ^{≤b}L ⟶ L`, and on `U`, where `K_n|_U` is in degrees `≤ b`
and `(τ^{>b}L)|_U` in degrees `> b`, composition with `(τ^{≤b}L)|_U ⟶ L|_U` is a bijection on
morphisms out of `K_n|_U`. Since `τ^{≤b}L` lies in `D^b_{Coh}(𝒪_X)`
(`AlgebraicGeometry.boundedCoherentDerived_truncLE_obj`), the statement for it is
[Stacks, Tag 0G2H], `AlgebraicGeometry.DeligneSystem.restrictionLifting`, and
`CategoryTheory.RestrictionLifting.of_comp` carries it to `L`. -/
public lemma restrictionLifting_of_derivedCategoryBPlus (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) L) :
    RestrictionLifting (D.system ⋙ (boundedCoherentDerived X).ι)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory L := by
  obtain ⟨a, b, -, -, hLE⟩ := D.exists_isGE_isLE_system
  let t := DerivedCategory.TStructure.t (C := X.Modules)
  let tU := DerivedCategory.TStructure.t (C := U.Modules)
  let R := (Scheme.Modules.restrictFunctor j).mapDerivedCategory
  let L' : BoundedCoherentDerived X :=
    ⟨(t.truncLE b).obj L, boundedCoherentDerived_truncLE_obj b L hL⟩
  have h₀ : RestrictionLifting (D.system ⋙ (boundedCoherentDerived X).ι) R
      ((t.truncLE b).obj L) :=
    (D.restrictionLifting L').map_source (boundedCoherentDerived X).ι (𝟭 _) R
      (Functor.rightUnitor _).symm (Iso.refl _)
  have hK : ∀ n : ℕ, t.IsLE ((D.system ⋙ (boundedCoherentDerived X).ι).obj (op n)) b :=
    fun n => (ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived X)
      DerivedCategory.TStructure.t (D.system.obj (op n)) b).mp (hLE (op n))
  let T := (t.triangleLEGT b).obj L
  refine h₀.of_comp ((t.truncLEι b).app L) (fun n f => ?_) (fun n => ?_)
  · exact ⟨t.liftTruncLE f b, (t.liftTruncLE_ι f b).symm⟩
  · have : tU.IsLE (R.obj ((D.system ⋙ (boundedCoherentDerived X).ι).obj (op n))) b :=
      isLE_mapDerivedCategory_obj _ _ b
    have : tU.IsGE (R.mapTriangle.obj T).obj₃ (b + 1) :=
      isGE_mapDerivedCategory_obj (Scheme.Modules.restrictFunctor j) ((t.truncGT b).obj L) (b + 1)
    exact tU.bijective_comp_mor₁_of_isLE_of_isGE (R.mapTriangle.obj T)
      (R.map_distinguished T (t.triangleLEGT_distinguished b L)) b _

/-- **Stacks Project, Tag 0G4K.** The result of [Stacks, Tag 0G2H] holds even for `L` in
`D^+_{Coh}(𝒪_X)`. Let `j : U ⟶ X` be an open immersion of Noetherian schemes, let `(K_n)` be a
Deligne system, identified on `U` by `e` with the constant system at `K`, and let `L` be an object
of `D(𝒪_X)` that is cohomologically bounded below with coherent cohomology sheaves. Then

`colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)`,

the map being the canonical one: the cocone of `CategoryTheory.restrictionHomCocone`, which sends
`g : K_n ⟶ L` to `K ≅ K_n|_U ⟶ L|_U`, is a colimit cocone.

This is `AlgebraicGeometry.DeligneSystem.restrictionLifting_of_derivedCategoryBPlus` read through
`CategoryTheory.RestrictionLifting.isColimitRestrictionHomCocone`. Nothing is assumed. -/
@[stacks 0G4K]
public theorem nonempty_isColimit_restrictionHomCocone (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) L) :
    Nonempty (IsColimit (restrictionHomCocone (D.system ⋙ (boundedCoherentDerived X).ι)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory L
      ((boundedCoherentDerived U).ι.obj K) e)) :=
  ⟨(D.restrictionLifting_of_derivedCategoryBPlus L hL).isColimitRestrictionHomCocone _ e⟩

/-- **A morphism out of the value of a Deligne system extends to a stage of the system.** For a
Deligne system `(K_n)` with value `K` on `U` and an object `L` of `D^b_{Coh}(𝒪_X)`, every
morphism `K ⟶ L|_U` is the restriction of a morphism `K_n ⟶ L` for some `n`, the source being
read through the identification `e` of `K_n|_U` with `K`. This is the surjectivity of the map of
[Stacks, Tag 0G2H], `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`. -/
public lemma exists_comp_restrict_eq (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    (L : BoundedCoherentDerived X)
    (φ : (boundedCoherentDerived U).ι.obj K ⟶ (restrictBoundedCoherent j).obj L) :
    ∃ (n : ℕᵒᵖ) (g : D.system.obj n ⟶ L),
      e.inv.app n ≫ (restrictBoundedCoherent j).map g = φ := by
  have := D.isIso_restrictionNatTrans K e
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective ((D.restrictionNatTrans K e).app L)).1
    inferInstance).2 φ
  obtain ⟨i, g, rfl⟩ := FunctorToTypes.jointly_surjective' _ L x
  exact ⟨Pro.liftedIndexDown i, g, (D.restrictionNatTrans_app_ι K e i L g).symm.trans hx⟩

end AlgebraicGeometry.DeligneSystem

end

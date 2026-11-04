module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietorisTriangle
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# The Mayer--Vietoris dévissage in the bounded below derived category

Let `X` be a scheme and, for an open `W` of `X`, write `P_W` for the endofunctor
`j_{W,*} j_W^*` of the `𝒪_X`-modules: restrict a module to the open subscheme `W`, then push
the result forward along the inclusion `j_W : W → X`.  For two opens `A`, `B` of `X` the
Mayer--Vietoris sequence

`0 ⟶ P_{A ∪ B} M ⟶ P_A M ⊕ P_B M ⟶ P_{A ∩ B} M ⟶ 0`

is short exact at every injective `𝒪_X`-module `M` ([Stacks, Tag 01EA]).  Applying the three
functors degreewise to a bounded below complex `K` of injective `𝒪_X`-modules therefore gives
a short exact sequence of complexes, hence a distinguished triangle

`P_{A ∪ B} K ⟶ P_A K ⊕ P_B K ⟶ P_{A ∩ B} K ⟶ (P_{A ∪ B} K)⟦1⟧`

in the bounded below derived category `D⁺(𝒪_X)`.  A triangulated subcategory of `D⁺(𝒪_X)`
closed under isomorphisms which contains the images of `P_A K`, `P_B K` and `P_{A ∩ B} K`
therefore contains the image of `P_{A ∪ B} K`; and since `P_⊤` is the identity functor it
contains the image of `K` itself as soon as `A ∪ B = X`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.prop_of_sup`: the dévissage for two arbitrary
  opens, whose first vertex is the image of `P_{A ∪ B} K`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.prop_of_top`: the image of `P_⊤ K` in `D⁺(𝒪_X)` is
  the image of `K`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.prop_of_isOpenCover_pair`: the dévissage for a
  cover of `X` by two opens, whose first vertex is the image of `K`.

## Implementation notes

Short exactness of the Mayer--Vietoris sequence of endofunctors is
`Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective`, and the passage
from a short exact sequence of additive functors to a distinguished triangle of the unbounded
derived category is `CategoryTheory.triangleOfInjectiveCochainComplex_distinguished`.  That
triangle is moved into `D⁺(𝒪_X)` along `DerivedCategory.Plus.ι`, which is fully faithful and
triangulated, so that `CategoryTheory.Functor.map_distinguished_iff` applies; its three vertices
are recognised through `DerivedCategory.quotientCompQhIso`, and the middle one is split by the
degreewise biproduct decomposition of the middle term of the sequence of complexes.

The endofunctors are written both as `j_{W,*} j_W^*` in Mathlib's vocabulary of modules on a
scheme and as the pullback--pushforward composite attached to the inclusion `j_W` read as a
morphism of ringed spaces; `restrictPushIso` is the isomorphism between the two.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

universe v₁ u₁ v₂ u₂ w u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-! ### Objects of the bounded below derived category -/

section Plus

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]

/-- The image in `D⁺(B)` of a bounded below complex, read in the unbounded derived category. -/
private def plusObjιIso (M : HomotopyCategory.Plus B) :
    DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj M) ≅
      DerivedCategory.Q.obj M.obj.as :=
  (DerivedCategory.quotientCompQhIso B).app M.obj.as

/-- An isomorphism of the underlying cochain complexes induces an isomorphism in `D⁺(B)`. -/
private def plusObjIso {M N : HomotopyCategory.Plus B} (e : M.obj.as ≅ N.obj.as) :
    DerivedCategory.Plus.Qh.obj M ≅ DerivedCategory.Plus.Qh.obj N :=
  DerivedCategory.Plus.ι.preimageIso
    (plusObjιIso M ≪≫ DerivedCategory.Q.mapIso e ≪≫ (plusObjιIso N).symm)

end Plus

/-! ### Transport of a distinguished triangle along a fully faithful functor -/

section TriangleTransport

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.Full] [Φ.Faithful]

omit [HasShift C ℤ] [HasShift D ℤ] [Φ.CommShift ℤ] [Φ.Faithful] in
/-- The first two commutative squares of the comparison of triangles below. -/
private lemma map_preimage_comm {Y Z : C} {Y' Z' : D} (f : Y' ⟶ Z')
    (e : Φ.obj Y ≅ Y') (e' : Φ.obj Z ≅ Z') :
    Φ.map (Φ.preimage (e.hom ≫ f ≫ e'.inv)) ≫ e'.hom = e.hom ≫ f := by
  rw [Φ.map_preimage, Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id]

omit [Φ.Faithful] in
/-- The third commutative square of the comparison of triangles below. -/
private lemma map_preimage_comm_shift {X Z : C} {X' Z' : D} (f : Z' ⟶ X'⟦(1 : ℤ)⟧)
    (e : Φ.obj X ≅ X') (e' : Φ.obj Z ≅ Z') :
    (Φ.map (Φ.preimage (e'.hom ≫ f ≫ (shiftFunctor D (1 : ℤ)).map e.inv ≫
          (Φ.commShiftIso (1 : ℤ)).inv.app X)) ≫
        (Φ.commShiftIso (1 : ℤ)).hom.app X) ≫ (shiftFunctor D (1 : ℤ)).map e.hom =
      e'.hom ≫ f := by
  rw [Φ.map_preimage]
  simp

end TriangleTransport

/-! ### The bounded below derived category -/

section Transport

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]

/-- Three objects of `D⁺(B)` whose images in `D(B)` are the vertices of a distinguished
triangle are themselves the vertices of a distinguished triangle: the inclusion of the bounded
below derived category is fully faithful and triangulated. -/
private lemma exists_distTriang_plus_of_iso
    (X₁ X₂ X₃ : DerivedCategory.Plus B) (T : Triangle (DerivedCategory B))
    (hT : T ∈ distTriang (DerivedCategory B))
    (e₁ : DerivedCategory.Plus.ι.obj X₁ ≅ T.obj₁)
    (e₂ : DerivedCategory.Plus.ι.obj X₂ ≅ T.obj₂)
    (e₃ : DerivedCategory.Plus.ι.obj X₃ ≅ T.obj₃) :
    ∃ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory.Plus B) := by
  refine ⟨DerivedCategory.Plus.ι.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv),
    DerivedCategory.Plus.ι.preimage (e₂.hom ≫ T.mor₂ ≫ e₃.inv),
    DerivedCategory.Plus.ι.preimage (e₃.hom ≫ T.mor₃ ≫
      (shiftFunctor (DerivedCategory B) (1 : ℤ)).map e₁.inv ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app X₁), ?_⟩
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
  · exact map_preimage_comm _ _ e₁ e₂
  · exact map_preimage_comm _ _ e₂ e₃
  · exact map_preimage_comm_shift _ _ e₁ e₃

/-- A triangulated subcategory of `D⁺(B)` closed under isomorphisms contains the biproduct of
two of its objects: the biproduct sits in the split distinguished triangle on them. -/
private lemma prop_biprod (P : ObjectProperty (DerivedCategory.Plus B))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] {Y Z : DerivedCategory.Plus B}
    (hY : P Y) (hZ : P Z) : P (Y ⊞ Z) :=
  P.ext_of_isTriangulatedClosed₂ (binaryBiproductTriangle Y Z)
    (binaryBiproductTriangle_distinguished Y Z) hY hZ

end Transport

/-! ### The dévissage attached to a short exact sequence of functors -/

section Devissage

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]
  {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]

/-- A short exact sequence of additive functors which is short exact at every injective object
gives, at a bounded below complex of injective objects, a distinguished triangle in `D⁺(B)`. -/
private lemma exists_distTriang_plus_of_shortExact (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
    (hinj : ∀ Z : A, Injective Z → (NatTrans.appShortComplex i q hiq Z).ShortExact)
    (K : HomotopyCategory.Plus A) (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) :
    ∃ (f : DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K) ⟶
          DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj K))
      (g : DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj K) ⟶
          DerivedCategory.Plus.Qh.obj (H.mapHomotopyCategoryPlus.obj K))
      (δ : DerivedCategory.Plus.Qh.obj (H.mapHomotopyCategoryPlus.obj K) ⟶
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K))⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory.Plus B) :=
  exists_distTriang_plus_of_iso _ _ _ _
    (triangleOfInjectiveCochainComplex_distinguished i q hiq hinj K.obj.as hK)
    (plusObjιIso _) (plusObjιIso _) (plusObjιIso _)

end Devissage

/-! ### The Mayer--Vietoris sequence of endofunctors of the modules on a scheme -/

section Scheme

variable {X : Scheme.{u}}

/-- The endofunctor `j_{W,*} j_W^*` of the `𝒪_X`-modules attached to an open `W` of `X`:
restrict to the open subscheme `W`, then push forward along its inclusion. -/
private def modRestrictPush (W : X.Opens) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Stacks.Duality.Coherator.pushRestrictFunctor W

/-- The middle term `j_{A,*} j_A^* ⊕ j_{B,*} j_B^*` of the Mayer--Vietoris sequence, as an
endofunctor of the `𝒪_X`-modules. -/
private def modMvMiddle (A B : X.Opens) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Stacks.Duality.Coherator.mvMiddleFunctor A B

private instance modRestrictPush_additive (W : X.Opens) : (modRestrictPush W).Additive :=
  inferInstanceAs (Stacks.Duality.Coherator.pushRestrictFunctor (X := X) W).Additive

private instance modMvMiddle_additive (A B : X.Opens) : (modMvMiddle A B).Additive :=
  inferInstanceAs (Stacks.Duality.Coherator.mvMiddleFunctor (X := X) A B).Additive

/-- The pair of the two restrictions `P_{A ∪ B} ⟶ P_A ⊕ P_B`. -/
private def modMvRes (A B : X.Opens) : modRestrictPush (A ⊔ B) ⟶ modMvMiddle A B :=
  Stacks.Duality.Coherator.mvResNat A B

/-- The difference of the two restrictions `P_A ⊕ P_B ⟶ P_{A ∩ B}`. -/
private def modMvDiff (A B : X.Opens) : modMvMiddle A B ⟶ modRestrictPush (A ⊓ B) :=
  Stacks.Duality.Coherator.mvDiffNat A B

private lemma modMvRes_comp_modMvDiff (A B : X.Opens) :
    modMvRes A B ≫ modMvDiff A B = 0 :=
  Stacks.Duality.Coherator.mvResNat_comp_mvDiffNat A B

/-- **The Mayer--Vietoris sequence of endofunctors is short exact at every injective
`𝒪_X`-module**, which is [Stacks, Tag 01EA] read on sections. -/
private lemma shortExact_modMv (A B : X.Opens)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (hM : Injective M) :
    (NatTrans.appShortComplex (modMvRes A B) (modMvDiff A B)
      (modMvRes_comp_modMvDiff A B) M).ShortExact :=
  Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective M hM A B

/-- The degreewise biproduct decomposition of the middle term of the Mayer--Vietoris sequence
of complexes. -/
private def modMvBicone (A B : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ) :
    BinaryBicone (((modRestrictPush A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
      (((modRestrictPush B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) where
  pt := ((modMvMiddle A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  fst := (Stacks.Duality.Coherator.mvBicone A B L).fst
  snd := (Stacks.Duality.Coherator.mvBicone A B L).snd
  inl := (Stacks.Duality.Coherator.mvBicone A B L).inl
  inr := (Stacks.Duality.Coherator.mvBicone A B L).inr
  inl_fst := (Stacks.Duality.Coherator.mvBicone A B L).inl_fst
  inl_snd := (Stacks.Duality.Coherator.mvBicone A B L).inl_snd
  inr_fst := (Stacks.Duality.Coherator.mvBicone A B L).inr_fst
  inr_snd := (Stacks.Duality.Coherator.mvBicone A B L).inr_snd

private def modMvBiconeIsBilimit (A B : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ) :
    (modMvBicone A B L).IsBilimit :=
  Stacks.Duality.Coherator.mvBiconeIsBilimit A B L

/-- Restriction to an open subscheme followed by the direct image along its inclusion is the
pullback--pushforward composite attached to that inclusion, read as a morphism of ringed
spaces. -/
private def restrictPushIso (W : X.Opens) :
    modulePullback W.ι.toLRSHom.toShHom ⋙ modulePushforward W.ι.toLRSHom.toShHom ≅
      modRestrictPush W :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm
    (Scheme.Modules.pushforward W.ι)

section Isos

variable (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- The two spellings of "restrict to `W` and push forward again" have the same image in
`D⁺(𝒪_X)`. -/
private def restrictPushPlusIso (W : X.Opens) :
    DerivedCategory.Plus.Qh.obj ((modulePullback W.ι.toLRSHom.toShHom ⋙
          modulePushforward W.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K) ≅
      DerivedCategory.Plus.Qh.obj ((modRestrictPush W).mapHomotopyCategoryPlus.obj K) :=
  plusObjIso ((NatIso.mapHomologicalComplex (restrictPushIso W) (ComplexShape.up ℤ)).app K.obj.as)

/-- The middle term of the Mayer--Vietoris sequence has the biproduct of the two outer
restrictions as its image in `D⁺(𝒪_X)`: the biproduct of complexes is formed degreewise and the
localization functors are additive. -/
private def mvMiddlePlusIso (A B : X.Opens) :
    DerivedCategory.Plus.Qh.obj ((modMvMiddle A B).mapHomotopyCategoryPlus.obj K) ≅
      DerivedCategory.Plus.Qh.obj ((modRestrictPush A).mapHomotopyCategoryPlus.obj K) ⊞
        DerivedCategory.Plus.Qh.obj ((modRestrictPush B).mapHomotopyCategoryPlus.obj K) :=
  DerivedCategory.Plus.ι.preimageIso
    (plusObjιIso ((modMvMiddle A B).mapHomotopyCategoryPlus.obj K) ≪≫
      biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves DerivedCategory.Q
        (modMvBiconeIsBilimit A B K.obj.as)) ≪≫
      biprod.mapIso (plusObjιIso ((modRestrictPush A).mapHomotopyCategoryPlus.obj K)).symm
        (plusObjιIso ((modRestrictPush B).mapHomotopyCategoryPlus.obj K)).symm ≪≫
      (DerivedCategory.Plus.ι.mapBiprod _ _).symm)

/-- For `W = ⊤` the endofunctor "restrict to `W` and push forward again" is the identity. -/
private def modTopIso :
    𝟭 (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ≅
      modRestrictPush (⊤ : X.Opens) :=
  Stacks.Duality.Coherator.pushRestrictTopIso

/-- Restricting to the whole of `X` and pushing forward again does not change the image in
`D⁺(𝒪_X)`. -/
private def topPlusIso :
    DerivedCategory.Plus.Qh.obj K ≅ DerivedCategory.Plus.Qh.obj
      ((modRestrictPush (⊤ : X.Opens)).mapHomotopyCategoryPlus.obj K) :=
  plusObjIso (((Functor.mapHomologicalComplexIdIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).app K.obj.as).symm ≪≫
    (NatIso.mapHomologicalComplex (modTopIso (X := X)) (ComplexShape.up ℤ)).app K.obj.as)

end Isos

/-! ### The dévissage -/

/-- **The Mayer--Vietoris dévissage.**  Let `A` and `B` be opens of a scheme `X`, write
`P_W` for the endofunctor "restrict to `W`, then push forward again" of the `𝒪_X`-modules, and
let `K` be a bounded below complex of injective `𝒪_X`-modules.  The Mayer--Vietoris sequence

`0 ⟶ P_{A ∪ B} K ⟶ P_A K ⊕ P_B K ⟶ P_{A ∩ B} K ⟶ 0`

is short exact, so a triangulated subcategory of `D⁺(𝒪_X)` closed under isomorphisms which
contains the images of `P_A K`, `P_B K` and `P_{A ∩ B} K` contains the image of
`P_{A ∪ B} K`. -/
theorem prop_of_sup
    (P : ObjectProperty (DerivedCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (A B : X.Opens)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (hA : P (DerivedCategory.Plus.Qh.obj ((modulePullback A.ι.toLRSHom.toShHom ⋙
      modulePushforward A.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))
    (hB : P (DerivedCategory.Plus.Qh.obj ((modulePullback B.ι.toLRSHom.toShHom ⋙
      modulePushforward B.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))
    (hC : P (DerivedCategory.Plus.Qh.obj ((modulePullback (A ⊓ B).ι.toLRSHom.toShHom ⋙
      modulePushforward (A ⊓ B).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) :
    P (DerivedCategory.Plus.Qh.obj ((modulePullback (A ⊔ B).ι.toLRSHom.toShHom ⋙
      modulePushforward (A ⊔ B).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)) := by
  have hmid : P (DerivedCategory.Plus.Qh.obj
      ((modMvMiddle A B).mapHomotopyCategoryPlus.obj K)) :=
    P.prop_of_iso (mvMiddlePlusIso K A B).symm
      (prop_biprod P (P.prop_of_iso (restrictPushPlusIso K A) hA)
        (P.prop_of_iso (restrictPushPlusIso K B) hB))
  obtain ⟨f, g, δ, hdist⟩ := exists_distTriang_plus_of_shortExact (modMvRes A B)
    (modMvDiff A B) (modMvRes_comp_modMvDiff A B)
    (fun M hM => shortExact_modMv A B M hM) K hK
  have hint : P (DerivedCategory.Plus.Qh.obj
      ((modRestrictPush (A ⊓ B)).mapHomotopyCategoryPlus.obj K)) :=
    P.prop_of_iso (restrictPushPlusIso K (A ⊓ B)) hC
  exact P.prop_of_iso (restrictPushPlusIso K (A ⊔ B)).symm
    (P.ext_of_isTriangulatedClosed₁ _ hdist hmid hint)

/-- **The Mayer--Vietoris dévissage at `W = ⊤`.**  Restricting a bounded below complex of
injective `𝒪_X`-modules to the whole of `X` and pushing it forward again does not change its
image in `D⁺(𝒪_X)`. -/
theorem prop_of_top
    (P : ObjectProperty (DerivedCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (h : P (DerivedCategory.Plus.Qh.obj ((modulePullback (⊤ : X.Opens).ι.toLRSHom.toShHom ⋙
      modulePushforward (⊤ : X.Opens).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) :
    P (DerivedCategory.Plus.Qh.obj K) :=
  P.prop_of_iso (topPlusIso K).symm (P.prop_of_iso (restrictPushPlusIso K (⊤ : X.Opens)) h)

/-- **The Mayer--Vietoris dévissage for a cover of `X` by two opens.**  If `A ∪ B = X` then the
first vertex of the Mayer--Vietoris triangle is `K` itself. -/
theorem prop_of_isOpenCover_pair
    (P : ObjectProperty (DerivedCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (A B : X.Opens) (hAB : A ⊔ B = ⊤)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (hA : P (DerivedCategory.Plus.Qh.obj ((modulePullback A.ι.toLRSHom.toShHom ⋙
      modulePushforward A.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))
    (hB : P (DerivedCategory.Plus.Qh.obj ((modulePullback B.ι.toLRSHom.toShHom ⋙
      modulePushforward B.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))
    (hC : P (DerivedCategory.Plus.Qh.obj ((modulePullback (A ⊓ B).ι.toLRSHom.toShHom ⋙
      modulePushforward (A ⊓ B).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) :
    P (DerivedCategory.Plus.Qh.obj K) := by
  refine prop_of_top P K hK ?_
  rw [← hAB]
  exact prop_of_sup P A B K hK hA hB hC

end Scheme

end Stacks.AlgebraicGeometry.ModuleBaseChange

end

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# Isomorphisms of `D⁺(X_étale)` are detected on affine étale schemes

Let `X` be a scheme. An object `C` of `D⁺(X_étale)` is zero as soon as, for every affine scheme `U`
étale over `X` and every `n`, the only morphism `ℤ_U[-n] ⟶ C|_U` is zero; consequently a morphism
`φ : E ⟶ E'` of `D⁺(X_étale)` is an isomorphism as soon as composition with `φ|_U` is bijective on
morphisms out of every `ℤ_U[-n]`. This is the form in which [Stacks, Tag 0F0B] deduces part (2)
from part (1): "every object of `X_étale` has an étale covering by quasi-compact and
quasi-separated objects".

## Main results

* `DerivedCategory.Plus.eq_zero_of_forall_singleFunctor_hom_eq_zero` — for `Y ∈ D^{≥b}`, morphisms
  `A ⟶ H^b(Y)` come from morphisms `A[-b] ⟶ Y`.
* `Stacks.Pretriangulated.eq_zero_of_surjective_of_injective` — morphisms into the cone of a map
  which is bijective on morphisms out of a test object and its shift vanish.
* `Stacks.EtaleCohomology.smallEtalePullbackAbSectionsIso` — the global sections of the restriction
  of a sheaf to an étale `U` are its sections over `U`.
* `Stacks.EtaleCohomology.isZero_of_forall_isAffine` — a sheaf vanishing over every affine object
  is zero.
* `Stacks.EtaleCohomology.isZero_of_forall_isAffine_hom_eq_zero` and
  `Stacks.EtaleCohomology.isIso_of_forall_isAffine_bijective` — **the detection statements**.

## Implementation notes

The detection statements quantify over the derived categories of all affine `U` étale over `X`, so
they fix one model of the derived category; it is the standard one, under which the base change
map `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` they are combined with is built.

## References

* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Pretriangulated

open CategoryTheory.Pretriangulated

variable {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

open ZeroObject in
/-- **Morphisms into the cone of a map which is bijective on morphisms out of a test object.** Let
`T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` be distinguished and `A ≅ A'⟦1⟧`. If composition with `T₁ ⟶ T₂` is
surjective on morphisms out of `A` and injective on morphisms out of `A'`, every morphism
`A ⟶ T₃` is zero. -/
theorem eq_zero_of_surjective_of_injective (T : Triangle 𝒟) (hT : T ∈ distTriang 𝒟)
    {A A' : 𝒟} (e : A ≅ A'⟦(1 : ℤ)⟧)
    (hsurj : Function.Surjective (fun y : A ⟶ T.obj₁ ↦ y ≫ T.mor₁))
    (hinj : Function.Injective (fun y : A' ⟶ T.obj₁ ↦ y ≫ T.mor₁)) (x : A ⟶ T.obj₃) :
    x = 0 := by
  let y : A' ⟶ T.obj₁ := (shiftFunctor 𝒟 (1 : ℤ)).preimage (e.inv ≫ x ≫ T.mor₃)
  have hy : y ≫ T.mor₁ = 0 ≫ T.mor₁ := by
    apply (shiftFunctor 𝒟 (1 : ℤ)).map_injective
    simp only [y, Functor.map_comp, Functor.map_preimage, Category.assoc,
      comp_distTriang_mor_zero₃₁ T hT, comp_zero, zero_comp, Functor.map_zero]
  have h3 : x ≫ T.mor₃ = 0 := by
    have : e.inv ≫ x ≫ T.mor₃ = 0 := by
      simpa [y] using show (shiftFunctor 𝒟 (1 : ℤ)).map y = 0 by rw [hinj hy, Functor.map_zero]
    simpa using e.hom ≫= this
  obtain ⟨z, rfl⟩ := Triangle.coyoneda_exact₃ T hT x h3
  obtain ⟨w, rfl⟩ := hsurj z
  simp [comp_distTriang_mor_zero₁₂ T hT]

end Stacks.Pretriangulated

namespace DerivedCategory.Plus

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **Morphisms into the lowest cohomology object are detected by morphisms out of single
objects.** Let `Y` in `D⁺(𝒜)` be `≥ b`. If every morphism `A[-b] ⟶ Y` vanishes, then every
morphism `A ⟶ H^b(Y)` vanishes: `τ_{≤b}Y` is `H^b(Y)` placed in degree `b`, and the inclusion
`τ_{≤b}Y ⟶ Y` is invertible on `H^b`. -/
theorem eq_zero_of_forall_singleFunctor_hom_eq_zero {Y : Plus 𝒜} {b : ℤ} [Y.IsGE b] {A : 𝒜}
    (h : ∀ x : (singleFunctor 𝒜 b).obj A ⟶ Y, x = 0)
    (φ : A ⟶ (homologyFunctor 𝒜 b).obj Y) : φ = 0 := by
  let τ := (TStructure.t.truncLE b).obj Y
  let ιτ := (TStructure.t.truncLEι b).app Y
  have hιτ : ∀ i, i ≤ b → IsIso ((homologyFunctor 𝒜 i).map ιτ) :=
    fun i hi ↦ isIso_homologyMap_truncLEι_app Y i b hi
  have : τ.IsGE b := by
    rw [isGE_iff]
    intro i hi
    have := hιτ i hi.le
    exact IsZero.of_iso (isZero_homology_of_isGE' Y b i hi)
      (asIso ((homologyFunctor 𝒜 i).map ιτ))
  obtain ⟨A', ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE τ b
  let sCH : singleFunctor 𝒜 b ⋙ homologyFunctor 𝒜 b ≅ 𝟭 𝒜 :=
    _root_.DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 b
  have := hιτ b le_rfl
  let f : A ⟶ A' := φ ≫ inv ((homologyFunctor 𝒜 b).map ιτ) ≫ (homologyFunctor 𝒜 b).map e.hom ≫
    sCH.hom.app A'
  have h0 : (homologyFunctor 𝒜 b).map ((singleFunctor 𝒜 b).map f) = 0 := by
    have := congrArg (homologyFunctor 𝒜 b).map (h ((singleFunctor 𝒜 b).map f ≫ e.inv ≫ ιτ))
    simp only [Functor.map_comp, Functor.map_zero] at this
    rwa [← cancel_mono ((homologyFunctor 𝒜 b).map e.inv ≫ (homologyFunctor 𝒜 b).map ιτ),
      zero_comp]
  have hf : f = 0 := by
    have hn := sCH.hom.naturality f
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [← cancel_epi (sCH.hom.app A), ← hn, h0, zero_comp, comp_zero]
  have : φ = f ≫ sCH.inv.app A' ≫ (homologyFunctor 𝒜 b).map e.inv ≫
      (homologyFunctor 𝒜 b).map ιτ := by
    simp only [f, Category.assoc, Iso.hom_inv_id_app_assoc, Functor.id_obj]
    simp [← Functor.map_comp_assoc]
  rw [this, hf, zero_comp]

end DerivedCategory.Plus

namespace Stacks.EtaleCohomology

section Restriction

variable {X : Scheme.{u}} (U : X.Etale)

/-- Inverse image along an étale morphism is restriction: `smallEtalePullbackAb` and
`Stacks.EtaleCohomology.etaleRestrictionAt` are both left adjoint to direct image. -/
def smallEtalePullbackAbIsoEtaleRestrictionAt {V : Scheme.{u}} (j : V ⟶ X) [Etale j] :
    smallEtalePullbackAb j ≅ etaleRestrictionAt j Ab.{u + 1} :=
  (smallEtaleAdjunctionAb j).leftAdjointUniq (smallEtaleRestrictionAdjunctionAt Ab.{u + 1} j)

/-- The terminal object of the small étale site of `U`, composed with `U ⟶ X`, is `U`. -/
def smallEtaleComposeTerminalIso :
    (Scheme.Etale.smallEtaleCompose U.hom).obj (Scheme.Etale.mk (𝟙 U.left)) ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp)

/-- **The global sections of the restriction of `G` to an étale `U` are the sections of `G` over
`U`.** -/
def smallEtalePullbackAbSectionsIso (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    ((smallEtalePullbackAb U.hom).obj G).obj.obj (op (Scheme.Etale.mk (𝟙 U.left))) ≅
      G.obj.obj (op U) :=
  ((sheafToPresheaf _ _).mapIso ((smallEtalePullbackAbIsoEtaleRestrictionAt U.hom).app G)).app
      (op (Scheme.Etale.mk (𝟙 U.left))) ≪≫
    G.obj.mapIso (smallEtaleComposeTerminalIso U).op.symm

end Restriction

/-- **An abelian sheaf on the small étale site vanishing over every affine object is zero**: the
affine objects form a cover-dense subsite, so the identity of the sheaf is determined by its
components there, where it agrees with the zero map. -/
theorem isZero_of_forall_isAffine {X : Scheme.{u}} (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (h : ∀ U : X.Etale, IsAffine U.left → ∀ s : G.obj.obj (op U), s = 0) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  have hw : Functor.whiskerLeft (AffineEtale.Spec X).op
        ((sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map (𝟙 G)) =
      Functor.whiskerLeft (AffineEtale.Spec X).op
        ((sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map (0 : G ⟶ G)) := by
    ext V s
    have hV : IsAffine ((AffineEtale.Spec X).obj V.unop).left :=
      inferInstanceAs (IsAffine (Spec _))
    exact (h _ hV _).trans (h _ hV _).symm
  refine (sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map_injective ?_
  rw [← Functor.IsCoverDense.sheafHom_eq (AffineEtale.Spec X) (K := smallEtaleTopology X)
    ((sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map (𝟙 G)), hw,
    Functor.IsCoverDense.sheafHom_eq]

-- The detection statement below quantifies over the derived categories of all affine étale
-- `U ⟶ X`, so it fixes one model; it is the standard one, under which
-- `smallEtaleDerivedBaseChangeAb` (`BaseChangeHigher/BaseChangeCondition.lean:256`), the base
-- change map its consumers combine it with, is built.
attribute [local instance] HasDerivedCategory.standard

/-- The constant abelian sheaf `ℤ` on the small étale site of a scheme. -/
abbrev constantZ (Y : Scheme.{u}) : Sheaf (smallEtaleTopology Y) Ab.{u + 1} :=
  (constantSheaf (smallEtaleTopology Y) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **The lowest cohomology sheaf vanishes when `C` is tested on affines.** If `C` is `≥ b` and for
every affine `U` étale over `X` and every `n` the only morphism `ℤ_U[-n] ⟶ C|_U` is zero, then
`H^b(C)` is zero. -/
private theorem isZero_homology_of_forall_isAffine_hom_eq_zero {X : Scheme.{u}}
    (C : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (h : ∀ (U : X.Etale), IsAffine U.left → ∀ (n : ℤ)
      (x : (DerivedCategory.Plus.singleFunctor _ n).obj (constantZ U.left) ⟶
        (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus.obj C), x = 0)
    (b : ℤ) [C.IsGE b] : IsZero ((DerivedCategory.Plus.homologyFunctor _ b).obj C) := by
  apply isZero_of_forall_isAffine
  intro U hU s
  let Y := (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus.obj C
  have hY : Y.IsGE b := by
    rw [DerivedCategory.Plus.isGE_iff]
    intro i hi
    exact IsZero.of_iso ((smallEtalePullbackAb U.hom).map_isZero
        (DerivedCategory.Plus.isZero_homology_of_isGE' C b i hi))
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso _ i).app C)
  let ε := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
    (smallEtalePullbackAb U.hom) b).app C
  let T : U.left.Etale := Scheme.Etale.mk (𝟙 U.left)
  let t : ((DerivedCategory.Plus.homologyFunctor _ b).obj Y).obj.obj (op T) :=
    ((sheafToPresheaf _ _).map ε.inv).app (op T)
      ((smallEtalePullbackAbSectionsIso U _).inv s)
  let ψ : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      ((DerivedCategory.Plus.homologyFunctor _ b).obj Y).obj.obj (op T) :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ t).comp AddEquiv.ulift.toAddMonoidHom)
  let adj := constantSheafAdj (smallEtaleTopology U.left) Ab.{u + 1}
    (isTerminalEtaleMkId U.left)
  have hφ := DerivedCategory.Plus.eq_zero_of_forall_singleFunctor_hom_eq_zero (h U hU b)
    ((adj.homEquiv _ _).symm ψ)
  have hψ : ψ = 0 := by
    rw [(adj.homEquiv _ _).symm_apply_eq.mp hφ, Adjunction.homEquiv_unit, Functor.map_zero,
      comp_zero]
  have ht : t = 0 := by
    rw [← show ψ.hom (ULift.up 1) = t from one_zsmul t, hψ]
    rfl
  have hs : (smallEtalePullbackAbSectionsIso U _).inv s = 0 := by
    simpa [t, ← NatTrans.comp_app_apply, ← Functor.map_comp] using
      congrArg (((sheafToPresheaf _ _).map ε.hom).app (op T)) ht
  simpa using congrArg (smallEtalePullbackAbSectionsIso U _).hom hs

open ZeroObject in
/-- **Objects of `D⁺(X_étale)` are detected on affine étale `U ⟶ X` by morphisms out of `ℤ`
placed in a single degree.** If for every affine `U` étale over `X` and every `n` the only morphism
`ℤ_U[-n] ⟶ C|_U` is zero, then `C` is zero: in the lowest degree `b` in which `C` has cohomology,
a section of `H^b(C)` over an affine `U` is a morphism `ℤ_U ⟶ H^b(C|_U)`, which comes from a
morphism `ℤ_U[-b] ⟶ C|_U` (`DerivedCategory.Plus.eq_zero_of_forall_singleFunctor_hom_eq_zero`),
and the affine objects form a cover-dense subsite (`isZero_of_forall_isAffine`). -/
theorem isZero_of_forall_isAffine_hom_eq_zero {X : Scheme.{u}}
    (C : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (h : ∀ (U : X.Etale), IsAffine U.left → ∀ (n : ℤ)
      (x : (DerivedCategory.Plus.singleFunctor _ n).obj (constantZ U.left) ⟶
        (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus.obj C), x = 0) :
    IsZero C := by
  obtain ⟨a, ha⟩ := C.property
  have hall : ∀ m : ℕ, C.IsGE (a + m) := by
    intro m
    induction m with
    | zero => simpa using (DerivedCategory.Plus.isGE_ι_obj_iff C a).1 ha
    | succ m ih =>
      rw [DerivedCategory.Plus.isGE_iff]
      intro i hi
      rcases (show i ≤ a + m by omega).lt_or_eq with hi' | rfl
      · exact DerivedCategory.Plus.isZero_homology_of_isGE' C (a + m) i hi'
      · exact isZero_homology_of_forall_isAffine_hom_eq_zero C h _
  have hH : ∀ i : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj C) := fun i ↦
    have := hall (i - a + 1).toNat
    DerivedCategory.Plus.isZero_homology_of_isGE' C (a + ((i - a + 1).toNat : ℤ)) i (by omega)
  have : IsIso (0 : C ⟶ 0) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    exact IsZero.isIso (hH n) (Functor.map_isZero _ (isZero_zero _)) _
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : C ⟶ 0))

section IsoDetection

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus

open Pretriangulated in
/-- **Isomorphisms of `D⁺(X_étale)` are detected on affine étale `U ⟶ X` by morphisms out of `ℤ`
placed in a single degree.** If for every affine `U` étale over `X` and every `n`, composition with
`φ|_U` is bijective on morphisms `ℤ_U[-n] ⟶ E|_U`, then `φ` is an isomorphism: the restriction to
`U` of a cone of `φ` receives only the zero morphism from every `ℤ_U[-n]`. -/
theorem isIso_of_forall_isAffine_bijective {X : Scheme.{u}}
    {E E' : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (φ : E ⟶ E')
    (h : ∀ (U : X.Etale), IsAffine U.left → ∀ n : ℤ, Function.Bijective
      (fun y : (DerivedCategory.Plus.singleFunctor _ n).obj (constantZ U.left) ⟶
          (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus.obj E ↦
        y ≫ (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle φ
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_forall_isAffine_hom_eq_zero _ fun U hU n x ↦ ?_)
  let F := (smallEtalePullbackAb U.hom).rightDerivedFunctorPlus
  exact Stacks.Pretriangulated.eq_zero_of_surjective_of_injective
    (F.mapTriangle.obj (Triangle.mk φ g δ)) (F.map_distinguished _ hT)
    (((DerivedCategory.Plus.singleFunctors _).shiftIso 1 n (n + 1) (by omega)).app
      (constantZ U.left)).symm (h U hU n).2 (h U hU (n + 1)).1 x

end IsoDetection

end Stacks.EtaleCohomology

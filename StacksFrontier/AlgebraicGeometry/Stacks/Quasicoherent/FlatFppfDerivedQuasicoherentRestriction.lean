module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFreeModules
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticColocalizationTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSemiorthogonalDecompositionOfClass
public import StacksFrontier.CategoryTheory.Triangulated.QuotientEquivalenceOfFullyFaithfulLeftAdjoint
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBIsoClosedInstance
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B9 (2)(a) and (2)(c): `g^*` and `Lg_!` between `D_{LQCoh^fbc}` and `D_QCoh`

Let `𝒳` be an algebraic stack, `g` the morphism of ringed topoi of **Stacks 0788** for the
flat-fppf site, with `g^*` restriction to the flat objects and `Lg_!` its left adjoint
(**Stacks 07AS**).  `LQCoh^fbc(𝒪_𝒳)` is the class with the flat base change property of
**Stacks 0762** read with the pullback of sheaves.

* (2)(a), `AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleRestriction`: `g^*`
  carries `D_{LQCoh^fbc}(𝒪_𝒳)` into `D_QCoh(𝒪_{𝒳_{flat,fppf}})`, by Stacks 07B1 (2)(b).
* (2)(c), over its input Stacks 07B3 (2),
  `AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleLowerShriek_of_single`: `Lg_!`
  carries `D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)` as soon as it carries the
  quasi-coherent modules in degree `0` there; this is the dévissage of the source through the
  truncations, using that `Lg_!` is right t-exact and commutes with direct sums and that
  `LQCoh^fbc(𝒪_𝒳)` is weak Serre and closed under colimits of sequences (Stacks 0771 (2), (5)).

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite WeakSerre

universe u w t t' u₁ v₁ w₁

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-- Mathlib's abelian structure on `Mod(𝒪_𝒳)`, met by instance search before the larger-universe
instances of the library, whose universe constraints it cannot solve at this site. -/
local instance instAbelianFppfModules (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Abelian (fppfModules B S hS 𝒳) :=
  SheafOfModules.instAbelian _

/-- Mathlib's abelian structure on `Mod(𝒪_{𝒳_{flat,fppf}})`; see the previous instance. -/
local instance instAbelianFlatFppfModules (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Abelian (flatFppfModules B S hS 𝒳) :=
  SheafOfModules.instAbelian _

/-- `instAbelianFppfModules` at the spelling of the source of
`AlgebraicGeometry.Stack.FlatFppf.moduleRestriction`. -/
local instance instAbelianAmbientModules (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ambientStructureSheaf B S hS 𝒳))) :=
  SheafOfModules.instAbelian _

/-- `instAbelianFppfModules` at the spelling of the fppf ringed topos. -/
local instance instAbelianFppfRingedToposModules (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O)) :=
  SheafOfModules.instAbelian _

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The quasi-coherent modules on the flat-fppf site of an algebraic stack,
`QCoh(𝒪_{𝒳_{flat,fppf}})`: the modules which are quasi-coherent on that ringed site in the sense
of Stacks 03DL. -/
abbrev flatQuasicoherentModules : ObjectProperty (flatFppfModules B S hS 𝒳) :=
  fun M => M.IsQuasicoherentOnSite

section Restriction

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]

/-- **Stacks 07B9** (2)(a).  For `K` in `D_{LQCoh^fbc}(𝒪_𝒳)` (with the flat base change property
of Stacks 0762 read with the pullback of sheaves), the restriction `g^*K` to the flat-fppf site
lies in `D_QCoh(𝒪_{𝒳_{flat,fppf}})`: `g^*` is exact, so `H^n(g^*K) = g^*H^n(K)`, which is
quasi-coherent by Stacks 07B1 (2)(b). -/
@[stacks 07B9 "part (2)(a): for K in D_LQCoh^fbc(𝒪_𝒳) the restriction g^*K to the flat-fppf \
site lies in D_QCoh(𝒪_{𝒳_flat,fppf}), for LQCoh^fbc with the flat base change property of \
Stacks 0762 read with the pullback of sheaves, at module universe u, for any models of the \
derived categories"]
theorem derivedCategoryB_derivedModuleRestriction (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K) :
    DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳)
      ((derivedModuleRestriction B S hS 𝒳).obj K) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((moduleRestriction B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).symm
    (isQuasicoherentOnSite_moduleRestriction _ (hK n))

/-- For `K` in `D_{LQCoh^fbc}(𝒪_𝒳)` (with the flat base change property of Stacks 0762 read with
the pullback of sheaves), `g^*K = 0` exactly when `K` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`:
`g^*K = 0` exactly when every cohomology module of `K` is parasitic
(`isZero_derivedModuleRestriction_iff_forall_isParasitic`, Stacks 07AR), and the `LQCoh^fbc` half
is the hypothesis on `K`. -/
@[stacks 07B9 "part (2)(b): for K in D_LQCoh^fbc(𝒪_𝒳), g^*K = 0 if and only if K lies in \
D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳), for LQCoh^fbc with the flat base change property of \
Stacks 0762 read with the pullback of sheaves, at module universe u, for any models of the \
derived categories"]
theorem isZero_derivedModuleRestriction_iff_derivedParasitic
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K) :
    IsZero ((derivedModuleRestriction B S hS 𝒳).obj K) ↔
      ParasiticQuotient.derivedParasitic B S hS 𝒳
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K :=
  (isZero_derivedModuleRestriction_iff_forall_isParasitic B S hS 𝒳 K).trans
    ⟨fun hp n => ⟨hp n, hK n⟩, fun hp n => (hp n).1⟩

end Restriction

/-- Quasi-coherence on the flat-fppf site is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_flatQuasicoherentModules :
    (flatQuasicoherentModules B S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e h := SheafOfModules.IsQuasicoherentOnSite.of_iso e h

/-- A Grothendieck abelian category has exact countable direct sums. -/
theorem hasExactCountableDirectSums_of_isGrothendieckAbelian {A : Type u₁} [Category.{v₁} A]
    [Abelian A] [IsGrothendieckAbelian.{w₁} A] : HasExactCountableDirectSums A := by
  have : HasColimitsOfSize.{w₁, w₁} A := IsGrothendieckAbelian.hasColimits A
  have : HasCoproducts.{w₁} A := fun _ => inferInstance
  have : AB4OfSize.{w₁} A := IsGrothendieckAbelian.ab4OfSize A
  have : HasCoproducts.{0} A := fun J => hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (Equiv.ulift.{w₁} (α := J)))
  let _ : AB4OfSize.{0} A := AB4OfSize_shrink.{0, w₁} A
  exact ⟨inferInstance, fun I _ => ⟨inferInstance, inferInstance⟩⟩

/-- Sheaves of modules on the flat-fppf site of an algebraic stack form a Grothendieck abelian
category, the site being essentially small. -/
instance isGrothendieckAbelian_flatFppfModules :
    IsGrothendieckAbelian.{u} (flatFppfModules B S hS 𝒳) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- `LQCoh^fbc(𝒪_𝒳)` is closed under colimits of sequences in `Mod(𝒪_𝒳)` (Stacks 0771 (5)). -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_colimit
    (F : ℕ ⥤ fppfModules B S hS 𝒳) [HasColimitsOfShape (AsSmall.{u} ℕ) (fppfModules B S hS 𝒳)]
    [HasColimit F]
    (hF : ∀ n, lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 (F.obj n)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 (colimit F) := by
  have := isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChangeFppf B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (AsSmall.{u} ℕ)
  have hP := (locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids).prop_colimit ((AsSmall.equiv.{0, 0, u} (C := ℕ)).inverse ⋙ F)
    (fun _ => hF _)
  exact ((isWeakSerre_of_isWeakSerreClass
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).isClosedUnderIsomorphisms
    ).of_iso (Functor.Final.colimitIso (AsSmall.equiv.{0, 0, u} (C := ℕ)).inverse F) hP

section LowerShriek

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]

/-- **Stacks 07B9** (2)(c), over its input Stacks 07B3 (2).  If `Lg_!` carries every
quasi-coherent module `H` of `Mod(𝒪_{𝒳_{flat,fppf}})`, put in degree `0`, into
`D_{LQCoh^fbc}(𝒪_𝒳)` (that is Stacks 07B3 (2)), then it carries all of
`D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)`.

This is the dévissage of the source: `Lg_!` is triangulated, right t-exact (its right adjoint
`g^*` is exact) and commutes with direct sums, `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory
closed under colimits of sequences (Stacks 0771 (2), (5)), and an object is the derived colimit
of its truncations (`DerivedCategory.derivedCategoryB_obj_of_isLE_obj`). -/
theorem derivedCategoryB_derivedModuleLowerShriek_of_single :
    (∀ M : flatFppfModules B S hS 𝒳, M.IsQuasicoherentOnSite →
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
        ((derivedModuleLowerShriek B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor (flatFppfModules B S hS 𝒳) 0).obj M))) →
    ∀ H : DerivedCategory (flatFppfModules B S hS 𝒳),
      DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳) H →
        DerivedCategoryB.derivedCategoryB
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
          ((derivedModuleLowerShriek B S hS 𝒳).obj H) := by
  intro h0 H hH
  have : IsGrothendieckAbelian.{u} (fppfModules B S hS 𝒳) :=
    isGrothendieckAbelian_fppfModules B S hS 𝒳
  have := AB5OfSize_shrink.{0, 0, u, u} (fppfModules B S hS 𝒳)
  have := AB5OfSize_shrink.{0, 0, u, u} (flatFppfModules B S hS 𝒳)
  have : PreservesColimitsOfShape (Discrete ℕ) (derivedModuleLowerShriek B S hS 𝒳) :=
    have := (derivedModuleLowerShriekAdjunction B S hS 𝒳).leftAdjoint_preservesColimits
    inferInstance
  exact DerivedCategory.derivedCategoryB_obj_of_isLE_obj (derivedModuleLowerShriek B S hS 𝒳)
    (isWeakSerre_of_isWeakSerreClass _)
    hasExactCountableDirectSums_of_isGrothendieckAbelian.{_, _, u}
    hasExactCountableDirectSums_of_isGrothendieckAbelian.{_, _, u}
    (fun X n _ => @DerivedCategory.isLE_obj_of_adjunction
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ambientStructureSheaf B S hS 𝒳)))
      _ (instAbelianAmbientModules B S hS 𝒳)
      (inferInstanceAs (HasDerivedCategory.{t} (fppfModules B S hS 𝒳)))
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (structureSheaf B S hS 𝒳)))
      _ (instAbelianFlatFppfModules B S hS 𝒳)
      (inferInstanceAs (HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)))
      (moduleRestriction B S hS 𝒳) (moduleRestriction_additive B S hS 𝒳)
      (moduleRestriction_preservesFiniteLimits B S hS 𝒳)
      (moduleRestriction_preservesFiniteColimits B S hS 𝒳) _
      (derivedModuleLowerShriekAdjunction B S hS 𝒳) X n _)
    (fun F hF => locallyQuasicoherentSheafFlatBaseChangeFppfModules_colimit B E h S hS 𝒳 F hF)
    (fun M hM q => DerivedCategory.derivedCategoryB_obj_singleFunctor
      (derivedModuleLowerShriek B S hS 𝒳) (flatQuasicoherentModules B S hS 𝒳) _ inferInstance
      h0 M hM q)
    H hH

/-- **Stacks 07B9** (2)(a) followed by (2)(c), over Stacks 07B3 (2): for `K` in
`D_{LQCoh^fbc}(𝒪_𝒳)`, the parasitic-free part `Lg_! g^* K` of Stacks 07BA lies in
`D_{LQCoh^fbc}(𝒪_𝒳)` again, provided `Lg_!` carries every quasi-coherent module of
`Mod(𝒪_{𝒳_{flat,fppf}})` in degree `0` into `D_{LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedSheafFlatBaseChange_parasiticFreePart_of_single :
    (∀ M : flatFppfModules B S hS 𝒳, M.IsQuasicoherentOnSite →
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
        ((derivedModuleLowerShriek B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor (flatFppfModules B S hS 𝒳) 0).obj M))) →
    ∀ K : DerivedCategory (fppfModules B S hS 𝒳),
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K →
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
        (parasiticFreePart B S hS 𝒳 (derivedModuleLowerShriek B S hS 𝒳) K) := by
  intro h0 K hK
  exact derivedCategoryB_derivedModuleLowerShriek_of_single B E h S hS 𝒳 h0 _
    (derivedCategoryB_derivedModuleRestriction B E h S hS 𝒳 K hK)

/-- **Stacks 07B9** (2)(d), over Stacks 07B3 (2).  Restriction `g^*` to the flat-fppf site and
`Lg_!` induce mutually inverse equivalences between `D_QCoh(𝒪_𝒳)` — the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of Stacks 07B6 — and
`D_QCoh(𝒪_{𝒳_{flat,fppf}})`, provided `Lg_!` carries every quasi-coherent module of the
flat-fppf site in degree `0` into `D_{LQCoh^fbc}(𝒪_𝒳)` (that is Stacks 07B3 (2)).

`g^*` induces the functor `c` by (2)(a) and (2)(b); `g^* Lg_! = id`; and the counit
`Lg_! g^* E ⟶ E` becomes an isomorphism after `g^*`, so its cone lies in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` by (2)(b) and the quotient functor inverts it
(`CategoryTheory.Pretriangulated.quotientEquivalenceOfLeftAdjoint`). -/
def derivedQuasicoherentEquivalenceOfSingle
    (h0 : ∀ M : flatFppfModules B S hS 𝒳, M.IsQuasicoherentOnSite →
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
        ((derivedModuleLowerShriek B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor (flatFppfModules B S hS 𝒳) 0).obj M))) :
    ParasiticQuotient.quotient B S hS 𝒳
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) ≌
      (DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳)).FullSubcategory :=
  haveI := isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳
  Pretriangulated.quotientEquivalenceOfLeftAdjoint (derivedModuleRestriction B S hS 𝒳)
    (derivedModuleLowerShriekAdjunction B S hS 𝒳)
    (DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳))
    (DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳))
    (ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳))
    (derivedCategoryB_derivedModuleRestriction B E h S hS 𝒳)
    (derivedCategoryB_derivedModuleLowerShriek_of_single B E h S hS 𝒳 h0)
    (fun X hX => (isZero_derivedModuleRestriction_iff_derivedParasitic B E h S hS 𝒳 X
      (fun n => (hX n).2)).2 hX)
    (ParasiticQuotient.toQuotient B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳))
    (fun X hX hX0 => (isZero_derivedModuleRestriction_iff_derivedParasitic B E h S hS 𝒳 X hX).1
      hX0)

end LowerShriek

end AlgebraicGeometry.Stack.FlatFppf


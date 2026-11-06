module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorParasiticKernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSummary
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSerreAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSmallness
public import StacksFrontier.CategoryTheory.Triangulated.HomologicalFunctor
public import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-!
# The cohomology functor on `D_QCoh(𝒪_𝒳)`

The cohomology functor `H^i : D_B(𝒜) ⟶ B` of a weak Serre subcategory, the equivalence of the
étale and fppf readings of `LQCoh^fbc(𝒪_𝒳)`, the triangulated structure of the Verdier quotient
`D_QCoh(𝒪_𝒳)`, and the cohomology functor `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of an algebraic stack
obtained by descending `Q ∘ H^i` through that quotient.

## Main definitions

* `DerivedCategoryB.homologyFunctorB`: the cohomology functor `D_B(𝒜) ⥤ B`.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfEquivEtale`: the equivalence of
  the fppf and étale readings of `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherent'`: the cohomology functor
  `H^i : D_QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`.

## Main results

* `DerivedCategoryB.isHomological_homologyFunctorB`: `H^i : D_B(𝒜) ⥤ B` is homological.
* `AlgebraicGeometry.Stack.isHomological_cohomologyDerivedCategoryQuasicoherent`: the descended
  `H^i` is homological.
* `AlgebraicGeometry.Stack.isZero_iff_forall_isZero_cohomologyDerivedCategoryQuasicoherent`: an
  object of `D_QCoh(𝒪_𝒳)` is zero if and only if all its cohomology objects vanish.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe vA uA u w t

namespace CategoryTheory.Localization

end CategoryTheory.Localization

namespace DerivedCategoryB

section HomologyFunctorB

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{t} A]
  (B : ObjectProperty A) [B.IsWeakSerreClass]

/-- **The cohomology functor `H^i : D_B(𝒜) ⟶ B` of a weak Serre subcategory.**  An object of
`D_B(𝒜)` has all its cohomology objects in `B` by definition, so the `i`-th cohomology functor
of `D(𝒜)` corestricts to the full subcategory `B`. -/
def homologyFunctorB (i : ℤ) :
    (derivedCategoryB B).FullSubcategory ⥤ B.FullSubcategory :=
  B.lift ((derivedCategoryB B).ι ⋙ DerivedCategory.homologyFunctor A i) fun X => X.property i

/-- The underlying object of `H^i(X)` in `𝒜` is the `i`-th cohomology object of the underlying
object of `X` in `D(𝒜)`. -/
@[simp]
theorem homologyFunctorB_obj_obj (i : ℤ) (X : (derivedCategoryB B).FullSubcategory) :
    ((homologyFunctorB B i).obj X).obj =
      (DerivedCategory.homologyFunctor A i).obj X.obj :=
  rfl

/-- `H^i : D_B(𝒜) ⟶ B` preserves zero morphisms. -/
instance preservesZeroMorphisms_homologyFunctorB (i : ℤ) :
    (homologyFunctorB B i).PreservesZeroMorphisms where
  map_zero X Y := by
    apply B.ι.map_injective
    exact (DerivedCategory.homologyFunctor A i).map_zero _ _

/-- **`H^i : D_B(𝒜) ⟶ B` is homological**, for `B` a weak Serre subcategory of `𝒜`.

The inclusion `D_B(𝒜) ⟶ D(𝒜)` is triangulated and the `i`-th cohomology functor of `D(𝒜)` is
homological, so a distinguished triangle of `D_B(𝒜)` goes to an exact short complex of `𝒜`; the
inclusion `B ⟶ 𝒜` is exact and faithful, so it reflects that exactness.

The hypothesis `[(derivedCategoryB B).IsTriangulated]`, which is what makes `D_B(𝒜)`
pretriangulated and the statement meaningful, is itself implied by `[B.IsWeakSerreClass]`:
it is `DerivedCategoryB.derivedCategoryB_isTriangulated` at
`WeakSerre.isWeakSerre_of_isWeakSerreClass`.  It is taken as an instance argument only because
`CategoryTheory.Functor.IsHomological` needs the pretriangulated structure already at
elaboration time. -/
instance isHomological_homologyFunctorB [(derivedCategoryB B).IsTriangulated] (i : ℤ) :
    (homologyFunctorB B i).IsHomological where
  exact T hT := by
    have : PreservesFiniteLimits B.ι := B.preservesFiniteLimits_ι_of_isWeakSerreClass
    have : PreservesFiniteColimits B.ι := B.preservesFiniteColimits_ι_of_isWeakSerreClass
    have : B.ι.PreservesHomology := ⟨B.preservesKernels_ι, B.preservesCokernels_ι⟩
    refine (ShortComplex.exact_map_iff_of_faithful _ B.ι).mp ?_
    exact Functor.map_distinguished_exact
      ((derivedCategoryB B).ι ⋙ DerivedCategory.homologyFunctor A i) T hT

end HomologyFunctorB

end DerivedCategoryB

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `LQCoh^fbc(𝒪_𝒳)` is closed under isomorphisms, in the fppf reading.  The
subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is *strictly* full: membership depends only on the
isomorphism class of the module.  Both conjuncts transport along an isomorphism of the
underlying presheaves of modules, by
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_of_iso`. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeFppfModules :
    (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e hF := isLocallyQuasicoherentWithFlatBaseChange_of_iso B E h S hS _ _
    ((SheafOfModules.forget _).mapIso e) hF

/-- `LQCoh^fbc(𝒪_𝒳)` is closed under isomorphisms, in the étale reading.  The same for
the subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` of the modules on the associated étale
site. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeEtaleModules :
    (locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e hF := isLocallyQuasicoherentWithFlatBaseChange_of_iso B E h S hS _ _
    ((SheafOfModules.forget _).mapIso e) hF

/-- Restriction to the associated étale site, corestricted to `LQCoh^fbc(𝒪_𝒳)`: the forward
functor of `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfEquivEtale`.
Membership is a condition on the underlying presheaf of modules, which restriction leaves
alone. -/
def fppfToEtaleLocallyQuasicoherentFlatBaseChange :
    (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).FullSubcategory ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  (locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳).lift
    ((locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).ι ⋙
      fppfToEtaleModules B S hS 𝒳) fun F => F.property

/-- **Stacks 0771 part (1)** read as a functor: a member of `LQCoh^fbc(𝒪_𝒳)` on the associated
étale site is already an fppf sheaf, hence a module on the fppf site, by
`AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange`.  Only the sheaf
condition is improved, so the functor is the identity on the underlying presheaves of modules. -/
def etaleToFppfLocallyQuasicoherentFlatBaseChange :
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ⥤
      (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).FullSubcategory where
  obj F := ⟨fppfModuleOfLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳 F.obj.val
    F.property, F.property⟩
  map f := ⟨⟨f.hom.val⟩⟩

/-- Going to the fppf site and coming back is the identity: neither direction touches the
underlying presheaf of modules, and `Presheaf.IsSheaf` is a proposition. -/
def locallyQuasicoherentFlatBaseChangeFppfUnitIso :
    𝟭 ((locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).FullSubcategory) ≅
      fppfToEtaleLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 ⋙
        etaleToFppfLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
    simp only [Functor.comp_map, Functor.id_map, Category.comp_id, Category.id_comp]
    rfl

/-- Improving the sheaf condition and forgetting it again is the identity, for the same
reason as `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfUnitIso`. -/
def locallyQuasicoherentFlatBaseChangeFppfCounitIso :
    etaleToFppfLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 ⋙
        fppfToEtaleLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 ≅
      𝟭 (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
    simp only [Functor.comp_map, Functor.id_map, Category.comp_id, Category.id_comp]
    rfl

/-- The two readings of `LQCoh^fbc(𝒪_𝒳)`, on the étale and on the fppf site, are equivalent.  The
subcategory of the modules on the associated étale site of an algebraic stack which are locally
quasi-coherent with the flat base change property is equivalent to the subcategory of the modules
on its fppf site cut out by the same condition.

Both functors are the identity on the underlying presheaf of modules: the condition is a
condition on that presheaf, restriction from the fppf to the étale site only forgets part of the
sheaf condition, and part (1) — a member of `LQCoh^fbc` is a sheaf for the fppf topology — puts
it back.  So the two composites are the identity functors on the nose, `Presheaf.IsSheaf` being a
proposition.

This is the identification that lets a statement about one reading of the subcategory be read as
a statement about the other; it is what stands between
`DerivedCategoryB.isHomological_homologyFunctorB` and the hypothesis `hHhom` below. -/
def locallyQuasicoherentFlatBaseChangeFppfEquivEtale :
    (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).FullSubcategory ≌
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  .mk (fppfToEtaleLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳)
    (etaleToFppfLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳)
    (locallyQuasicoherentFlatBaseChangeFppfUnitIso B E h S hS 𝒳)
    (locallyQuasicoherentFlatBaseChangeFppfCounitIso B E h S hS 𝒳)

/-! ### The base statements, over an assumed abelian structure and the size conditions

The declarations of this section are the original statements of this file, kept verbatim: they
take the abelian structure of `Mod(𝒪_𝒳)` as an instance binder, and the three size conditions
`hls`, `hlsD`, `hwp` of the special adjoint functor theorem as hypotheses.  The primed
declarations of the sections after this one are the same constructions at the canonical abelian
structure `SheafOfModules.instAbelian` of `Mod(𝒪_𝒳)`, with the size conditions, the strict
fullness of `LQCoh^fbc(𝒪_𝒳)` and the Serre property of the parasitic modules discharged. -/

section AssumedAbelian

variable [Abelian (fppfModules B S hS 𝒳)] [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

section Cohomology

variable [EssentiallySmall.{u} 𝒳.val.val.obj]
  [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  [(locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).IsClosedUnderIsomorphisms]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsWeakSerreClass]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u}
    (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u}
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))

end Cohomology

end AssumedAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`, the subcategory
the Verdier quotient of **Stacks 07B6** divides by.  Inside `D_{LQCoh^fbc}(𝒪_𝒳)` the condition
is that all cohomology modules be parasitic, by
`AlgebraicGeometry.Stack.inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange`. -/
abbrev derivedParasiticSubcategory'
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)] : ObjectProperty
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).inverseImage
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι

/-- **The cohomology functor `H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`.**  It sends a complex
to the `i`-th cohomology module of the underlying object of `D(𝒪_𝒳)`, restricted to the
associated étale site; that this is locally quasi-coherent with the flat base change property is
the defining property of `D_{LQCoh^fbc}(𝒪_𝒳)` in degree `i`. -/
def cohomologyLocallyQuasicoherentFlatBaseChange' (i : ℤ) :
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  (locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳).lift
    ((derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι ⋙
      DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) i ⋙
        fppfToEtaleModules B S hS 𝒳)
    (fun X => X.property i)

/-! ### The triangulated structure of the Verdier quotient

`CategoryTheory.Functor.IsHomological` asks for the pretriangulated structure of its source at
elaboration time, so a statement that `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` is cohomological cannot
even be written down before `D_QCoh(𝒪_𝒳)` carries one.  Mathlib puts one on the localization of
a triangulated category at a morphism property which has a left calculus of fractions and is
compatible with triangulation (`CategoryTheory.Triangulated.Localization.pretriangulated`), and
both of those are *propositions about the morphism property*.  So they transport along the
equality `AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory` by
`rw`, and the instance then fires on `AlgebraicGeometry.Stack.derivedQuasicoherentW` itself — no
data is carried across the two spellings of the quotient, which is what makes this work where
rewriting the type of a functor would not. -/

/-- `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is closed under isomorphism, the parasitic modules being
so in every degree. -/
instance isClosedUnderIsomorphisms_derivedParasiticLocallyQuasicoherentFlatBaseChange :
    (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
      𝒳).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB _

/-- `D_{Parasitic}(𝒪_𝒳)` is closed under isomorphism. -/
instance isClosedUnderIsomorphisms_derivedParasiticModules :
    (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB _

/-- `D_{Parasitic}(𝒪_𝒳)` is a triangulated subcategory of `D(𝒪_𝒳)`, the parasitic modules being
a weak Serre class by **Stacks 0774** part (2). -/
instance isTriangulated_derivedParasiticModules :
    (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _)

section QuotientTriangulated

variable [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]

/-- The class of morphisms the Verdier quotient of **Stacks 07B6** inverts is the one attached
to the subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`: taking the cone in
the ambient `D(𝒪_𝒳)` and taking it inside the subcategory give the same class. -/
theorem derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory :
    derivedQuasicoherentW B E h S hS 𝒳
      = (derivedParasiticSubcategory' B E h S hS 𝒳).trW := by
  rw [derivedQuasicoherentW_eq_trW,
    inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange]

/-- The morphisms inverted by the Verdier quotient are compatible with triangulation, which is
what puts a pretriangulated structure on `D_QCoh(𝒪_𝒳)`. -/
instance isCompatibleWithTriangulation_derivedQuasicoherentW :
    (derivedQuasicoherentW B E h S hS 𝒳).IsCompatibleWithTriangulation := by
  rw [derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory B E h S hS 𝒳]
  infer_instance

/-- The morphisms inverted by the Verdier quotient admit a left calculus of fractions. -/
instance hasLeftCalculusOfFractions_derivedQuasicoherentW :
    (derivedQuasicoherentW B E h S hS 𝒳).HasLeftCalculusOfFractions := by
  rw [derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory B E h S hS 𝒳]
  infer_instance

/-- Every arrow of `D_QCoh(𝒪_𝒳)` is isomorphic to the image of an arrow of
`D_{LQCoh^fbc}(𝒪_𝒳)`, the quotient functor being a localization. -/
instance essSurj_mapArrow_toDerivedCategoryQuasicoherent :
    (toDerivedCategoryQuasicoherent B E h S hS 𝒳).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (derivedQuasicoherentW B E h S hS 𝒳)

end QuotientTriangulated

section Cohomology

variable [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u}
    (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))

/-- The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of **Stacks 0778** for an algebraic stack,
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` at the structure functor of `𝒳`. -/
abbrev quasicoheratorOfStack' :
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    hinc hclosed hpres (locallySmall_quasicoherentOfStack B S hS 𝒳)
    (locallySmall_flatBaseChangeOfStack B E h S hS 𝒳)
    (wellPowered_op_quasicoherentOfStack B S hS 𝒳 hsep) hsep

/-- **The functor `Q ∘ H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`** which the Verdier quotient of
**Stacks 07B6** descends to the cohomology functor of **Stacks 07B7**: take the `i`-th
cohomology module of a complex and apply the coherator to it. -/
def cohomologyQuasicoherent' (i : ℤ) :
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  cohomologyLocallyQuasicoherentFlatBaseChange' B E h S hS 𝒳 i ⋙
    quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep

/-- **`Q ∘ H^i` inverts the morphisms the Verdier quotient of Stacks 07B6 inverts.**

A morphism of `D_{LQCoh^fbc}(𝒪_𝒳)` is inverted by that quotient when its cone has parasitic
cohomology.  By the kernel computation `hQker` of **Stacks 0779** such a cone is sent to zero by
`Q ∘ H^i` in every degree, so the subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` lies in the
homological kernel of `Q ∘ H^i`, and the universal property of the Verdier quotient for
homological functors (**Stacks 05RJ**) produces a factorization through the quotient; a functor
isomorphic to one factoring through a localization inverts the same morphisms. -/
theorem isInvertedBy_cohomologyQuasicoherent' (i : ℤ)
    (hhom : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    (derivedQuasicoherentW B E h S hS 𝒳).IsInvertedBy
      (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i) := by
  have := hhom
  have hker : derivedParasiticSubcategory' B E h S hS 𝒳 ≤
      (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
        i).homologicalKernel := by
    intro X hX n
    exact (hQker _).mpr (((derivedParasiticSubcategory' B E h S hS 𝒳).le_shift n X hX) i)
  have hinv : (derivedParasiticSubcategory' B E h S hS 𝒳).trW.IsInvertedBy
      (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i) := by
    obtain ⟨H, fac, -, -⟩ := VerdierQuotientUniversalProperty.homological_universal_property
      (derivedParasiticSubcategory' B E h S hS 𝒳)
      (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i) hker
    refine (MorphismProperty.IsInvertedBy.iff_of_iso _ fac).mp (fun X Y f hf => ?_)
    have : IsIso ((derivedParasiticSubcategory' B E h S hS 𝒳).trW.Q.map f) :=
      Localization.inverts _ _ f hf
    change IsIso (H.map ((derivedParasiticSubcategory' B E h S hS 𝒳).trW.Q.map f))
    infer_instance
  rw [derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory B E h S hS 𝒳]
  exact hinv

/-- **Stacks 07B7.** The cohomology functor

`H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`

on the derived category of `𝒪_𝒳`-modules with quasi-coherent cohomology sheaves of an algebraic
stack `𝒳`.  It is the descent through the Verdier quotient of **Stacks 07B6** of the functor
`Q ∘ H^i` on `D_{LQCoh^fbc}(𝒪_𝒳)`, which is possible because that functor inverts the morphisms
the quotient inverts.

No `stacks` attribute: this form carries the coherator's inputs as hypotheses; Stacks 07B7 is
registered unconditionally at the sheaf reading in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherentCohomologySheaf.lean`. -/
def cohomologyDerivedCategoryQuasicoherent' (i : ℤ)
    (hhom : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  Localization.lift (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i)
    (isInvertedBy_cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
      hhom hQker)
    (derivedQuasicoherentW B E h S hS 𝒳).Q

/-- **Stacks 07B7**, the identity defining the cohomology functor: composed with the quotient
functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)`, the functor `H^i` of **Stacks 07B7** is the functor
`Q ∘ H^i` it descends.

No `stacks` attribute: this form carries the coherator's inputs as hypotheses; Stacks 07B7 is
registered unconditionally at the sheaf reading in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherentCohomologySheaf.lean`. -/
def cohomologyDerivedCategoryQuasicoherentFac' (i : ℤ)
    (hhom : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙
        cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
          i hhom hQker ≅
      cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i :=
  Localization.fac _ _ _

/-- **Stacks 07B7: the descended `H^i` is a cohomological functor.**  The functor

`H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`

carries a distinguished triangle of the Verdier quotient to an exact short complex of
`QCoh(𝒪_𝒳)`, which is what the source means by saying that one obtains a cohomological functor
on `D_QCoh(𝒪_𝒳)`.

The quotient functor is a localization at a class of morphisms compatible with triangulation, so
it is triangulated, commutes with the shift and is essentially surjective on arrows; a functor
out of such a localization is homological as soon as its composite with the localization functor
is (`CategoryTheory.Functor.isHomological_of_localization`).  That composite is `Q ∘ H^i` up to
the defining identity
`AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherentFac'`, and it is homological by
`hhom`.

No `stacks` attribute: this form carries the coherator's inputs as hypotheses; Stacks 07B7 is
registered unconditionally at the sheaf reading in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherentCohomologySheaf.lean`. -/
theorem isHomological_cohomologyDerivedCategoryQuasicoherent (i : ℤ)
    (hhom : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    (cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
      hhom hQker).IsHomological :=
  have := hhom
  Functor.isHomological_of_localization (toDerivedCategoryQuasicoherent B E h S hS 𝒳)
    (cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i hhom hQker)
    (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i)
    (cohomologyDerivedCategoryQuasicoherentFac' B E h S hS 𝒳 hinc hclosed hpres hsep i
      hhom hQker)

/-- **The cohomology functor of Stacks 07B7 is unique up to a unique isomorphism.**  Any functor
out of `D_QCoh(𝒪_𝒳)` whose composite with the quotient functor is identified with `Q ∘ H^i` is
isomorphic to `H^i` by exactly one isomorphism compatible with the two identifications. -/
theorem cohomologyDerivedCategoryQuasicoherent_uniq' (i : ℤ)
    (hhom : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val)
    (G : derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
    (α : toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙ G ≅
      cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i) :
    ∃! e : G ≅ cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
        i hhom hQker,
      Functor.whiskerLeft (toDerivedCategoryQuasicoherent B E h S hS 𝒳) e.hom ≫
          (cohomologyDerivedCategoryQuasicoherentFac' B E h S hS 𝒳 hinc hclosed hpres hsep
            i hhom hQker).hom = α.hom :=
  Localization.existsUnique_isoLift _ _ _ _ G α

/-- **The vanishing criterion of Stacks 07B7.**  An object `E` of `D_QCoh(𝒪_𝒳)` is zero if and
only if `H^i(E) = 0` for every `i : ℤ`.

The quotient functor is essentially surjective, so it suffices to treat the image of a complex
`Y` of `D_{LQCoh^fbc}(𝒪_𝒳)`, for which `H^i` of that image is `Q(H^i(Y))` by the defining
identity `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherentFac'`.  Then `hQker`
(**Stacks 0779** part (1)) turns the vanishing of all `Q(H^i(Y))` into `Y` having parasitic
cohomology modules, that is into `Y` lying in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, and
**Stacks 05RK** — `CategoryTheory.ObjectProperty.`
`kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel` — says that the kernel of the quotient
functor is the *least* strictly full saturated triangulated subcategory containing that
subcategory.  Membership of the subcategory in the kernel gives the "if" direction; leastness,
applied to the homological kernel of `Q ∘ H^i` (**Stacks 05RD**), gives the "only if"
direction.

No `stacks` attribute: this form carries the coherator's inputs as hypotheses; Stacks 07B7 is
registered unconditionally at the sheaf reading in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherentCohomologySheaf.lean`. -/
theorem isZero_iff_forall_isZero_cohomologyDerivedCategoryQuasicoherent
    (hhom : ∀ i : ℤ, (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val)
    (X : derivedCategoryQuasicoherent B E h S hS 𝒳) :
    IsZero X ↔ ∀ i : ℤ,
      IsZero ((cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
        (hhom i) hQker).obj X) := by
  haveI : (derivedQuasicoherentW B E h S hS 𝒳).Q.IsLocalization
      (derivedParasiticSubcategory' B E h S hS 𝒳).trW := by
    rw [← derivedQuasicoherentW_eq_trW_derivedParasiticSubcategory B E h S hS 𝒳]
    infer_instance
  obtain ⟨-, hleast⟩ :=
    (derivedParasiticSubcategory' B E h S hS
        𝒳).kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel
      (derivedQuasicoherentW B E h S hS 𝒳).Q
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y, Nonempty ((toDerivedCategoryQuasicoherent B E h S hS 𝒳).obj Y ≅ X) :=
    ⟨_, ⟨(toDerivedCategoryQuasicoherent B E h S hS 𝒳).objObjPreimageIso X⟩⟩
  have hzero : IsZero X ↔ IsZero ((toDerivedCategoryQuasicoherent B E h S hS 𝒳).obj Y) :=
    ⟨fun hz => hz.of_iso e, fun hz => hz.of_iso e.symm⟩
  have hdeg : ∀ i : ℤ,
      IsZero ((cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
          (hhom i) hQker).obj X) ↔
        IsZero ((cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i).obj Y) := by
    intro i
    have ei := ((cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
      (hhom i) hQker).mapIso e.symm).trans
        ((cohomologyDerivedCategoryQuasicoherentFac' B E h S hS 𝒳 hinc hclosed hpres hsep i
          (hhom i) hQker).app Y)
    exact ⟨fun hz => hz.of_iso ei.symm, fun hz => hz.of_iso ei⟩
  rw [hzero]
  constructor
  · intro hz i
    rw [hdeg i]
    haveI := hhom i
    obtain ⟨htri, hsat⟩ := Functor.isTriangulated_and_isSaturated_homologicalKernel
      (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i)
    have hsub : (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i).homologicalKernel
        ∈ {P' : ObjectProperty
            (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory |
          P'.IsClosedUnderIsomorphisms ∧ P'.IsTriangulated ∧ P'.IsSaturated ∧
            derivedParasiticSubcategory' B E h S hS 𝒳 ≤ P'} :=
      ⟨inferInstance, htri, hsat, fun Z hZ n =>
        (hQker _).mpr (((derivedParasiticSubcategory' B E h S hS 𝒳).le_shift n Z hZ) i)⟩
    have hmem := hleast.2 hsub Y hz
    exact (hmem 0).of_iso ((cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep
      i).mapIso ((shiftFunctorZero _ ℤ).app Y).symm)
  · intro hz
    exact hleast.1.2.2.2 Y fun i => (hQker _).mp ((hdeg i).mp (hz i))

/-! ### Discharging `hhom` and `hQker` from Stacks 0779

**Stacks 0779** is in the library.  It identifies the kernel of the coherator `Q` with the
parasitic modules and proves `Q` exact, which is exactly what `hQker` and the coherator half of
`hhom` ask for.  Both of its assertions are, however, stated *over the chart data of the
construction of `Q` in **Stacks 0778***: a functor `r : LQCoh^fbc(𝒪_𝒳) ⥤ 𝒜` standing for the
restriction `𝓕 ↦ 𝓕|_{U_étale}` along a smooth surjective chart `f : U → 𝒳`, together with
`hrpar`, `hrcounit`, `hreq` and, for exactness, `hrfincolim`.  The source does *not* assume that
data in **Stacks 07B7** — it has it because it builds `Q` from a chart in **Stacks 0778**,
whereas the coherator of this library is the abstract right adjoint of the special adjoint
functor theorem.

So the declarations of this section carry `r` and are deliberately **not** registered for
**Stacks 07B7**: registering them would make the tag stand for a statement conditional on data
the source's statement does not mention.  The registered declarations above keep `hhom` and
`hQker` as hypotheses, which is what the source assumes. -/

section ChartData

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
  (r : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids ⥤ 𝒜)
  (hrpar : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsZero (r.obj F) ↔ IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val)
  (hrcounit : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsIso (r.map ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres (locallySmall_quasicoherentOfStack B S hS 𝒳)
      (locallySmall_flatBaseChangeOfStack B E h S hS 𝒳)
      (wellPowered_op_quasicoherentOfStack B S hS 𝒳 hsep) hsep).counit.app F)))
  (hreq : (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc ⋙ r).IsEquivalence)

include hinc hrpar hrcounit hreq in
/-- **`hQker` is Stacks 0779 part (1).**  The kernel of the coherator
`AlgebraicGeometry.Stack.quasicoheratorOfStack'` is exactly the parasitic part of
`LQCoh^fbc(𝒪_𝒳)`, so the hypothesis `hQker` of the declarations registered for **Stacks 07B7**
above is discharged.

`AlgebraicGeometry.Stack.quasicoheratorOfStack'` is
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` at the structure functor of `𝒳`, by
definition and not up to a comparison, so this is literally
`AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic`; no bridge between
the two spellings of the coherator is needed.  The chart data `r`, `hrpar`, `hrcounit`, `hreq`
is the one **Stacks 0779** carries. -/
theorem isZero_quasicoheratorOfStack_iff_isParasitic
    (F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    IsZero ((quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).obj F) ↔
      IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val :=
  isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    (locallySmall_quasicoherentOfStack B S hS 𝒳) (locallySmall_flatBaseChangeOfStack B E h S hS 𝒳)
    (wellPowered_op_quasicoherentOfStack B S hS 𝒳 hsep) hsep r hrpar hrcounit hreq F

section Homological

variable [Abelian (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
  𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)]

omit hrpar in
include hinc hrcounit hreq in
/-- **`hhom` reduces to the homologicality of `H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`.**
The composite `Q ∘ H^i` is homological as soon as `H^i` is, because the coherator is exact:
**Stacks 0779** part (3), `AlgebraicGeometry.Stack.exact_flatBaseChangeQuasicoherator`, whose
left-exactness half is unconditional and whose right-exactness half is the chart data.  The
composition of a homological functor with an exact functor of abelian categories is
**Stacks 05QZ** (2), `main_statement_comp_homological_exact`.

What is left over is the hypothesis `hHhom`, the homologicality of `H^i` *before* the coherator;
together with the ambient `Abelian LQCoh^fbc(𝒪_𝒳)` instance it is the content of
**Stacks 0771** part (2) — `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)`, hence
abelian with exact inclusion.  What this library has of **Stacks 0771** is parts (1) and (4)(b),
in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/`, file
`LocallyQuasicoherentFlatBaseChangeSummary.lean`, and condition (2) of **Stacks 0754** for
part (2), above. -/
theorem isHomological_cohomologyQuasicoherent (i : ℤ)
    (hHhom : (cohomologyLocallyQuasicoherentFlatBaseChange' B E h S hS 𝒳 i).IsHomological)
    (hrfincolim : PreservesFiniteColimits r) :
    (cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i).IsHomological := by
  have := hHhom
  -- Both target categories carry a second, canonical `Preadditive` instance, the one every
  -- full subcategory of a preadditive category has.  The exactness lemma below reads its
  -- additivity hypothesis off the ambient `Abelian` instances instead, so pin the two
  -- `Preadditive` structures to those before anything about zero morphisms is stated.
  letI : Preadditive (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := Abelian.toPreadditive
  letI : Preadditive (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids) := Abelian.toPreadditive
  have hQzero : (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres
      hsep).PreservesZeroMorphisms :=
    have : (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).IsRightAdjoint :=
      (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids hinc hclosed hpres (locallySmall_quasicoherentOfStack B S hS 𝒳)
        (locallySmall_flatBaseChangeOfStack B E h S hS 𝒳)
        (wellPowered_op_quasicoherentOfStack B S hS 𝒳 hsep) hsep).isRightAdjoint
    inferInstance
  have hQexact := exact_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres
    (locallySmall_quasicoherentOfStack B S hS 𝒳) (locallySmall_flatBaseChangeOfStack B E h S hS 𝒳)
    (wellPowered_op_quasicoherentOfStack B S hS 𝒳 hsep) hsep r hrcounit hreq hrfincolim
  have hQlim : PreservesFiniteLimits
    (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep) := hQexact.1
  have hQcolim : PreservesFiniteColimits (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres
    hsep) := hQexact.2
  have hQadd : (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep).Additive :=
    letI : HasFiniteLimits (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := Abelian.hasFiniteLimits
    letI : HasBinaryProducts (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
      hasLimitsOfShape_of_hasFiniteLimits _ (Discrete WalkingPair)
    letI : PreservesLimitsOfShape (Discrete WalkingPair)
        (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep) :=
      PreservesFiniteLimits.preservesFiniteLimits _
    Functor.additive_of_preserves_binary_products _
  exact main_statement_comp_homological_exact
    (cohomologyLocallyQuasicoherentFlatBaseChange' B E h S hS 𝒳 i)
    (quasicoheratorOfStack' B E h S hS 𝒳 hinc hclosed hpres hsep)

include hinc hrpar hrcounit hreq in
/-- **The cohomology functor of Stacks 07B7 over the chart data of Stacks 0778.**  The functor
`AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherent'` with `hhom` and `hQker`
discharged by **Stacks 0779**: `hQker` outright, and `hhom` down to the homologicality of
`H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`.

This declaration is **not** registered for **Stacks 07B7**: it assumes the chart data `r`,
`hrpar`, `hrcounit`, `hreq`, `hrfincolim` of the construction of the coherator in
**Stacks 0778**, which the source's statement of **Stacks 07B7** does not mention. -/
def cohomologyDerivedCategoryQuasicoherentOfChart (i : ℤ)
    (hHhom : (cohomologyLocallyQuasicoherentFlatBaseChange' B E h S hS 𝒳 i).IsHomological)
    (hrfincolim : PreservesFiniteColimits r) :
    derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  cohomologyDerivedCategoryQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i
    (isHomological_cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hsep
      r hrcounit hreq i hHhom hrfincolim)
    (isZero_quasicoheratorOfStack_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres hsep r
      hrpar hrcounit hreq)

include hinc hrpar hrcounit hreq in
/-- **The defining identity of Stacks 07B7 over the chart data of Stacks 0778.**  Composed with
the quotient functor, `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherentOfChart` is
the functor `Q ∘ H^i` it descends.  Untagged for the same reason as that functor. -/
def cohomologyDerivedCategoryQuasicoherentOfChartFac (i : ℤ)
    (hHhom : (cohomologyLocallyQuasicoherentFlatBaseChange' B E h S hS 𝒳 i).IsHomological)
    (hrfincolim : PreservesFiniteColimits r) :
    toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙
        cohomologyDerivedCategoryQuasicoherentOfChart B E h S hS 𝒳 hinc hclosed hpres hsep r
          hrpar hrcounit hreq i hHhom hrfincolim ≅
      cohomologyQuasicoherent' B E h S hS 𝒳 hinc hclosed hpres hsep i :=
  cohomologyDerivedCategoryQuasicoherentFac' B E h S hS 𝒳 hinc hclosed hpres hsep i
    (isHomological_cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hsep
      r hrcounit hreq i hHhom hrfincolim)
    (isZero_quasicoheratorOfStack_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres hsep r
      hrpar hrcounit hreq)

end Homological

end ChartData

end Cohomology

end AlgebraicGeometry.Stack

end

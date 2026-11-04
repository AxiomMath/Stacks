module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionBySumsOfExtensionsByZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionForKFlatness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Triangle
public import StacksFrontier.Homology.KFlat.FinitelyPresented
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackOnRingedSpaces
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Part (1) of the stalk criterion for K-flatness on a ringed site

Let `(C, O)` be a ringed site and `K` a K-flat complex of `O`-modules.  Part (1) of
Stacks 0DEN asserts that the stalk complex `K_Φ` is a K-flat complex of modules over the
stalk ring `O_Φ`, at every point `Φ` of the site.  Part (2), the converse under the
hypothesis that the site has enough points, is
  `Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`.

This file carries out the source's proof of part (1) down to two named obligations, and
proves everything else.

## Main definitions

* `Stacks.Sheaves.KFlatStalkCriterion.StalkFlatOfSumExtensionByZero`: that the stalk of a direct
  sum of extensions
  by zero `j_{U!}O_U` is a flat module over the stalk ring.
* `Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic`: part (1) for a complex that is K-flat
  *and acyclic*.
* `Stacks.Sheaves.KFlatStalkCriterion.StalkRealizesFinitelyPresented`: that every finitely
  presented module over
  the stalk ring is the stalk of a sheaf of `O`-modules.  This is not consumed here; it is the
  input the source uses inside `StalkKFlatOfAcyclic`, recorded so that the obligation is
  traceable to the tags it comes from.

## Main results

* `Stacks.Sheaves.KFlatStalkCriterion.kFlat_stalkComplex_of_isSum`: the stalk of a bounded above
  complex whose
  terms are direct sums of extensions by zero is K-flat.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlat_stalkComplex_colimit`: hence so is the stalk of the
  077J resolution.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat`: **part (1) of Stacks 0DEN**, granted
  `StalkFlatOfSumExtensionByZero` and `StalkKFlatOfAcyclic`.  Its conclusion and its hypothesis
  on `K` are in the shape `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.StalkKFlat`
    consumes, so discharging those two
  obligations closes Stacks 0DEP.

## Implementation notes

**The route taken here is not the source's, and it avoids three predicates that this
development has no inhabitant for.**  Where the source says "any pullback of `L` is K-flat,
see Lemma 0G7E, in particular the stalk `L_Φ` is K-flat",
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex`
is available in this tree only on the three hypotheses `PullbackPreservesIsFlat` (Stacks 05VD),
`PullbackPreservesShortExact` (Stacks 0G6R) and `CyclesIsFlat` (Stacks 0G7C), of which only the
last is concluded anywhere —
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`, unconditionally.  The other two
are concluded by no declaration in either tree.  0G7E is also stated for a
`RingedToposSiteHom`, which a point of the site is not presented as.

The observation that removes all of that: the resolution of Stacks 06YS is built by Stacks 077J
as a sequential colimit of bounded above complexes whose terms are *direct sums of extensions by
zero of the structure sheaves of slices*, and
  `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit` forgets
that, exposing only the flatness it implies.  Restoring it — `exists_resolution_colimit_isSum`
below is the same proof with `term_isSum` kept — means the only flatness needed on the stalk
side is the flatness of the stalk of `j_{U!}O_U`, which is `StalkFlatOfSumExtensionByZero`.  That
is a computation about one explicit sheaf, not Stacks 05VD, and it is strictly weaker than
Stacks 05VB (flat sheaf, flat stalk), which this tree also lacks: `Stacks.IsFlatModuleStalk` is
defined at `Algebra/Category/ModuleCat/Sheaf/ModuleStalkFunctor.lean:397` with no theorem
concluding it.

Everything above the flatness of the terms then runs on machinery already present: the generic
K-flatness engines `CochainComplex.KFlat.kFlat_of_flat` (bounded above with flat terms, Stacks
064K) and `CochainComplex.KFlat.kFlat_colimit` (Stacks 06Y3), together with
`CochainComplex.KFlat.preservesColimit_mapHomologicalComplex` and the colimit-preservation of
the stalk functor, `Stacks.preservesColimits_sheafModuleFiberOfCommRing`.

**Universes.** Everything is at a single universe `u`, with `Category.{u} C`.  This is the
narrowing `Stacks.SheafOfModules.KFlatResolution` carries (`SmallCategory.{u} C`) and that
  `Stacks.Sheaves.KFlatStalkCriterion` and
`Stacks.SheafOfModules.SitePointStalkSheafify` already carry; it is forced by
  `Stacks.SheafOfModules.Tensor.ringSheaf` and it is not decided
here.

**No tag is placed in this file.**  Nothing here states part (1) under the hypotheses of
Stacks 0DEN: the results carry `StalkFlatOfSumExtensionByZero`, which is a `Prop` with no
inhabitant in this development, so a tag would be a weakening.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06Y3](https://stacks.math.columbia.edu/tag/06Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

universe u

namespace Stacks.Sheaves.KFlatStalkCriterion

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-! ### The two obligations -/

/-- **The stalk of `j_{U!}O_U` is flat**, and so is the stalk of a direct sum of such.

This is the only flatness input part (1) needs on the stalk side, and it is where the source
invokes Stacks 0G7E.  It is strictly weaker than Stacks 05VB, which asserts the same for an
arbitrary flat sheaf of modules: the sheaves quantified over here are the explicit generators
`j_{U!}O_U`, whose stalk at `Φ` is the free `O_Φ`-module on the fibre of `Φ` at `U`. -/
def StalkFlatOfSumExtensionByZero (Φ : J.Point.{u}) : Prop :=
  ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O),
    Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves O M →
      Module.Flat (structureStalk O Φ) ((Stacks.sheafModuleFiberOfCommRing Φ O).obj M)

/-- **Every finitely presented `O_Φ`-module is a stalk.**

This is the source's "we may assume there exists an `O`-module `F` such that `M ≅ F_Φ`",
which it reaches from Stacks 05N7 (a finitely presented module over a filtered colimit of
rings descends to a stage) followed by Stacks 0E8K (restriction of a K-flat complex to a
slice site is K-flat) replacing `C, O, K` by `C/U, O_U, K|_U`.  It is stated here as the
conclusion of that reduction rather than as its two steps, so that it mentions no slice site;
Stacks 0E8K has no declaration in this tree. -/
def StalkRealizesFinitelyPresented (Φ : J.Point.{u}) : Prop :=
  ∀ M : ModuleCat.{u} (structureStalk O Φ),
    Module.FinitePresentation (structureStalk O Φ) M →
      ∃ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O),
        Nonempty (M ≅ (Stacks.sheafModuleFiberOfCommRing Φ O).obj F)

/-! ### The 077J resolution, with the sum property of its terms kept -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The resolution of Stacks 06YS, presented as a sequential colimit and remembering that
its terms are direct sums of extensions by zero.**

This is `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit` with one clause not
  forgotten:  that proof
derives `AlgebraicGeometry.SheafOfModules.IsFlat ((D.obj n).X i)` from
`term_isSum` and keeps only the flatness.
The sum property is what transports to the stalk; sheaf flatness does not, for want of Stacks
05VB. -/
theorem exists_resolution_colimit_isSum
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (f : colimit D ⟶ G),
      (∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b) ∧
      (∀ (n : ℕ) (i : ℤ),
        Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves O
          ((D.obj n).X i)) ∧
      QuasiIso f := by
  obtain ⟨L⟩ :=
    Stacks.DerivedTensor.ResolutionByExtensionsByZero.exists_resolutionByDirectSumsExtensionsByZero
      O G
  exact ⟨L.system, L.colimitComparison, L.boundedAbove, L.term_isSum, L.colimit_quasiIso⟩

/-! ### Boundedness transports to the stalk -/

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The stalk functor is additive, so it carries a zero object to a zero object; hence a
complex strictly bounded above by `b` has stalk complex strictly bounded above by `b`. -/
lemma isStrictlyLE_stalkComplex (Φ : J.Point.{u})
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b] : (stalkComplex O Φ L).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi ↦ Functor.map_isZero (Stacks.sheafModuleFiberOfCommRing Φ O)
    (L.isZero_of_isStrictlyLE b i hi)

/-! ### K-flatness of the stalk of one stage of the resolution -/

/-- **The stalk of a bounded above complex of direct sums of extensions by zero is K-flat.**
Its terms are flat `O_Φ`-modules by `StalkFlatOfSumExtensionByZero`, and a bounded above
complex of flat modules is K-flat by Stacks 064K. -/
theorem kFlat_stalkComplex_of_isSum {Φ : J.Point.{u}}
    (hflat : StalkFlatOfSumExtensionByZero O Φ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b]
    (hL : ∀ i : ℤ,
      Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves O
        (L.X i)) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ L) := by
  have : (stalkComplex O Φ L).IsStrictlyLE b := isStrictlyLE_stalkComplex O Φ L b
  have : ∀ n : ℤ, Module.Flat (structureStalk O Φ) ((stalkComplex O Φ L).X n) :=
    fun n ↦ hflat _ (hL n)
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} _ b

/-- **The stalk of the 077J resolution is K-flat**: the stalk functor commutes with the
sequential colimit, each stage has K-flat stalk by `kFlat_stalkComplex_of_isSum`, and
K-flatness passes to a filtered colimit by Stacks 06Y3. -/
theorem kFlat_stalkComplex_colimit {Φ : J.Point.{u}}
    (hflat : StalkFlatOfSumExtensionByZero O Φ)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hsum : ∀ (n : ℕ) (i : ℤ),
      Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves O
        ((D.obj n).X i)) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ (colimit D)) := by
  let stalkFunctor : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      ModuleCat.{u} (structureStalk O Φ) := Stacks.sheafModuleFiberOfCommRing Φ O
  let : stalkFunctor.Additive := Stacks.additive_sheafModuleFiberOfCommRing Φ O
  let : PreservesColimitsOfSize.{0, 0} stalkFunctor :=
    Stacks.preservesColimits_sheafModuleFiberOfCommRing Φ O
  have := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D stalkFunctor
  have hstage : ∀ n : ℕ, CochainComplex.KFlat.{u, u}
      ((D ⋙ stalkFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj n) := fun n ↦ by
    obtain ⟨b, _⟩ := hLE n
    exact kFlat_stalkComplex_of_isSum O hflat (D.obj n) b (hsum n)
  exact CochainComplex.KFlat.of_iso
    (preservesColimitIso (stalkFunctor.mapHomologicalComplex (ComplexShape.up ℤ)) D).symm
    (CochainComplex.KFlat.kFlat_colimit.{u, 0, 0, u} _ hstage)

/-! ### The reduction to the acyclic case -/

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **The acyclic case of part (1), as a hypothesis.** The stalk of a complex of `O`-modules
which is both K-flat and acyclic is K-flat.

This is where the source's proof of part (1) descends after the mapping-cone reduction
(`kFlatStalk_of_kFlat` below carries that reduction out), and it is the whole of what part (1)
still needs beyond `StalkFlatOfSumExtensionByZero`.  The source closes it from Stacks 0E8F (a
complex whose tensor product with every finitely presented module is acyclic is K-flat), Stacks
05N7 and Stacks 0E8K — the last two being `StalkRealizesFinitelyPresented` above — together with
Stacks 03EL, which is available as `Stacks.SheafOfModules.SitePointStalkSheafify.stalkTensorData`
  and carried through
totalisation by `Stacks.Sheaves.KFlatStalkCriterion.totalStalkIso`. -/
def StalkKFlatOfAcyclic (Φ : J.Point.{u}) : Prop :=
  ∀ M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ,
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor O) M → M.Acyclic →
      CochainComplex.KFlat.{u, u} (stalkComplex O Φ M)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The colimit of the 077J ladder is K-flat as a complex of `O`-modules: its terms are flat
because they are direct sums of extensions by zero (Stacks 03EX), and a sequential colimit of
bounded above complexes of flat modules is K-flat (Stacks 06YS). -/
theorem kFlat_colimit_of_isSum
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hsum : ∀ (n : ℕ) (i : ℤ),
      Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves O
        ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor O) (colimit D) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat O D hLE
    (fun n i ↦
      Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves O _
        (hsum n i))

/-- **Part (1) of Stacks 0DEN, reduced to its acyclic case.**

The source's proof: resolve `K` by `Λ = colim D` with `α : Λ ⟶ K` a quasi-isomorphism, `D` a
sequence of bounded above complexes of direct sums of extensions by zero (Stacks 077J/06YS).
Then `Λ_Φ` is K-flat by `kFlat_stalkComplex_colimit`; the mapping cone `C(α)` is K-flat, being
the third vertex of a distinguished triangle whose first two vertices are (Stacks 07A3), and it
is acyclic because `α` is a quasi-isomorphism; so `C(α)_Φ` is K-flat by the acyclic case.  The
stalk functor is additive, so it carries the mapping cone of `α` to the mapping cone of `α_Φ`
(`CochainComplex.mappingCone.mapHomologicalComplexIso`), and `K_Φ` is the second vertex of the
distinguished triangle of `α_Φ`, whose other two vertices are now known K-flat — Stacks 06Y2. -/
theorem kFlatStalk_of_kFlat {Φ : J.Point.{u}}
    (hflat : StalkFlatOfSumExtensionByZero O Φ)
    (hacyc : StalkKFlatOfAcyclic O Φ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat O K) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ K) := by
  obtain ⟨D, α, hLE, hsum, hqis⟩ := exists_resolution_colimit_isSum O K
  let stalkFunctor : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      ModuleCat.{u} (structureStalk O Φ) := Stacks.sheafModuleFiberOfCommRing Φ O
  let : stalkFunctor.Additive := Stacks.additive_sheafModuleFiberOfCommRing Φ O
  -- `HasHomotopyCofiber` is seated by hand, one instance at a time: searching for it from
  -- scratch runs past the instance budget, because it has to rediscover
  -- `HasBinaryBiproducts` on sheaves of modules through `Abelian` at every mention of a
  -- mapping cone below.
  have hbb : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    inferInstance
  have hhc : HomologicalComplex.HasHomotopyCofiber α := inferInstance
  have hhc' : HomologicalComplex.HasHomotopyCofiber
      ((stalkFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := inferInstance
  -- The mapping cone of `α` is K-flat and acyclic, hence has K-flat stalk.
  have hcone : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor O)
      (CochainComplex.mappingCone α) :=
    CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ _ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished α)
      (kFlat_colimit_of_isSum O D hLE hsum) hK
  have hconeStalk : CochainComplex.KFlat.{u, u}
      (stalkComplex O Φ (CochainComplex.mappingCone α)) :=
    hacyc _ hcone (CategoryTheory.Functor.acyclic_mappingCone α hqis)
  -- The stalk of the mapping cone is the mapping cone of the stalk.
  have hconeStalk' : CochainComplex.KFlat.{u, u}
      (CochainComplex.mappingCone
        ((stalkFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
    CochainComplex.KFlat.of_iso
      (CochainComplex.mappingCone.mapHomologicalComplexIso α stalkFunctor) hconeStalk
  exact (CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished
      ((stalkFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map α))).2.1
    (kFlat_stalkComplex_colimit O hflat D hLE hsum) hconeStalk'

end Tensor

end Stacks.Sheaves.KFlatStalkCriterion

end

end

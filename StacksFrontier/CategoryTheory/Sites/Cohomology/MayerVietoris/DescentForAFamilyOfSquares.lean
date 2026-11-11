module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Square
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DescentForACoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TwoOutOfThree
import StacksCore.Tactic.StacksAttribute

/-!
# Descent for a coarser topology, detected by a family of squares

Let `C` carry two Grothendieck topologies `J' ≤ J` and let `𝒪` be a sheaf of rings for `J`, so
that `𝒪` is also a sheaf of rings for `J'` and the identity functor of `C` is a morphism of
ringed sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`, whose direct image `ε_*` is the identity on
underlying presheaves and whose inverse image `ε^{-1}` is `J`-sheafification.

Let `A` be a set and for each `α ∈ A` let

```
E α ⟶ Y α
  ↓      ↓
Z α ⟶ X α
```

be a commutative square in `C`. Suppose that this family of squares *detects* `J`-sheaves among
`J'`-sheaves, in the sense that a `J'`-sheaf of sets `F'` is a `J`-sheaf as soon as
`F'(X α) = F'(Z α) ×_{F'(E α)} F'(Y α)` for every `α`, and suppose that the canonical comparison
maps `c^{K'}_{X α, Z α, Y α, E α}` of [Stacks, Tag 0F16] are isomorphisms for every object `K'`
of `D(𝒪_{J'})` in the essential image of `Rε_*`. Then an object of `D⁺(𝒪_{J'})` lies in the
essential image of `Rε_*` precisely when all those comparison maps are isomorphisms for it.

## Main results

* `Stacks.Cohomology.MayerVietoris.essImage_iff_forall_isCSquareIso`: **Stacks 0F18.**
* `Stacks.Cohomology.MayerVietoris.isZero_of_forall_isCSquareIso_of_modulePullback_isZero`: the
  heart of the proof, that an object of `D⁺(𝒪_{J'})` all of whose comparison maps are
  isomorphisms and whose inverse image vanishes is itself zero.
* `Stacks.Cohomology.MayerVietoris.isSheaf_of_forall_isPullback`: the family of squares detects
  `J`-sheaves among `J'`-sheaves of sets in *any* universe, not only in `Type max u w`, which is
  the universe the detection hypothesis is stated in.
* `Stacks.Cohomology.MayerVietoris.isPullback_sections_homology`: for an object of `D(𝒪)` whose
  cohomology vanishes below a degree `n`, invertibility of the comparison map of a square makes
  the sections of the `n`-th cohomology sheaf over the square a pullback square of abelian
  groups.

## Implementation notes

The proof is the source's. An object `K'` of `D⁺(𝒪_{J'})` whose comparison maps are all
isomorphisms sits in a distinguished triangle `K' ⟶ Rε_* ε^{-1} K' ⟶ M' ⟶ K'[1]` whose first
arrow is the unit of the derived adjunction `ε^{-1} ⊣ Rε_*`. The middle term is in the essential
image of `Rε_*`, so by hypothesis and the two-out-of-three property of [Stacks, Tag 0EWP] the
object `M'` also has all its comparison maps invertible; and `ε^{-1} M' = 0` because `Rε_*` is
fully faithful, which is how `ε^{-1} R ε_* = id` is expressed here. The conclusion then follows
from the vanishing criterion: an object of `D⁺(𝒪_{J'})` with invertible comparison maps and
vanishing inverse image is zero.

That criterion is an induction on the lowest possibly nonzero degree. If `H^i(K') = 0` for
`i < n`, then the canonical triangle of [Stacks, Tag 0F16] for the square at `α`, together with
the vanishing of the cohomology of derived sections below `n`, gives a left exact sequence

```
0 ⟶ Γ(X α, H^n K') ⟶ Γ(Z α, H^n K') ⊕ Γ(Y α, H^n K') ⟶ Γ(E α, H^n K')
```

which says precisely that the sections of `H^n(K')` over the square form a pullback square. The
detection hypothesis then makes `H^n(K')` a `J`-sheaf, so it is in the essential image of `ε_*`,
so the unit of `ε^{-1} ⊣ ε_*` is invertible on it; and `ε^{-1} H^n(K') = H^n(ε^{-1} K') = 0`
because `ε^{-1}` is exact. Hence `H^n(K') = 0`.

Two points need more than the source says.

The detection hypothesis is stated for `J'`-sheaves of sets in `Type max u w`, the universe in
which a sheaf on a site with objects in `Type u` and homs in `Type w` is representable, whereas
it has to be applied to the underlying sheaf of sets of a sheaf of `𝒪`-modules, which lives in
the independent module universe `v`. `isSheaf_of_forall_isPullback` removes that gap: a
`J'`-sheaf of sets in any universe satisfying the pullback condition is a `J`-sheaf. The
argument generates, inside the given sheaf, the smallest subfunctor containing a prescribed
family of sections and closed under restriction, under amalgamation along `J'`-coverings and
under the pullback property of the squares. `DescentWitness` is the inductive syntax of those
three closure operations; the subfunctor it cuts out is `max u w`-small, is a `J'`-sheaf, and
has the pullback property at each square, so the hypothesis applies to it after shrinking. Both
the separatedness and the amalgamation half of the `J`-sheaf condition for the ambient sheaf are
obtained by applying this to a subfunctor generated by the relevant finitely many sections.

The derived adjunction `ε^{-1} ⊣ Rε_*` is obtained from `Adjunction.derived`, which asks for a
left derived functor on one side and a right derived functor on the other. The left-hand side is
`ε^{-1}` itself: it is exact, so `Functor.mapDerivedCategory` is its own left derived functor.
Full faithfulness of `Rε_*` is then `Adjunction.fullyFaithfulROfCompIsoId` applied to the
isomorphism `Rε_* ⋙ ε^{-1} ≅ id`, which comes from the counit of the underlying adjunction being
invertible — `ε_*` is fully faithful — and the uniqueness of right derived functors.

`Rε_*` is taken as an arbitrary right derived functor of `ε_*` with its unit, rather than a
chosen construction, as in `Stacks.Cohomology.MayerVietoris.isCSquareIso_ofLe_of_isPushout`.

The coarser sheaf of rings is written `Stacks.Sites.CoarserTopology.ringSheafOfLe h 𝒪` rather
than `(Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)`. The two are the same sheaf of
rings and the identification is used freely, but only the former is the literal codomain of
`ε_*`, and typeclass inference for sheaves of modules over the latter does not see through to
the instances registered for the former — the additivity and exactness of `ε_*` and `ε^{-1}`
are then unavailable. The statements below are therefore phrased with `ringSheafOfLe`, and the
one place where the coarser *ringed site* is needed, namely the comparison condition
`Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.IsCSquareIso`, is instantiated
at `(Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)`.

Degreewise sections of a complex followed by homology in degree `n`, and the degree-`n` short
complex followed by sections, are the same object of `AddCommGrpCat`, but only after
`HomologicalComplex.homology`, `HomologicalComplex.homologyFunctor` and the two
`shortComplexFunctor`s unfold. Tactics check type-correctness at a transparency that does not
unfold them, so every rewrite in `isPullback_sections_homology` is refused until those four
definitions are made reducible, which is what the `attribute [local implicit_reducible]`
declaration does.

## References

* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0F17](https://stacks.math.columbia.edu/tag/0F17)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EWP](https://stacks.math.columbia.edu/tag/0EWP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Sites.CoarserTopology
open Stacks.MayerVietoris

namespace Stacks.Cohomology.MayerVietoris

universe u v w r

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] HomologicalComplex.homology
  HomologicalComplex.homologyFunctor HomologicalComplex.shortComplexFunctor

/-! ### Right derived functors and K-injective complexes -/

section DerivedGeneralities

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian 𝒜] [HasDerivedCategory 𝒜]

/-- The identity of the image of a K-injective complex is a terminal object of the category of
arrows from the localization functor to it: by K-injectivity every derived morphism out of the
homotopy category into it is the image of a homotopy class, uniquely. -/
def isTerminalCostructuredArrowOfIsKInjective (I : CochainComplex 𝒜 ℤ)
    [I.IsKInjective] :
    IsTerminal (CostructuredArrow.mk
      (𝟙 (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I)))) := by
  let lift (arrow : CostructuredArrow DerivedCategory.Qh
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I))) :=
    (CochainComplex.IsKInjective.Qh_map_bijective arrow.left I).surjective arrow.hom
  refine IsTerminal.ofUniqueHom (fun arrow =>
    CostructuredArrow.homMk (lift arrow).choose (by simpa using (lift arrow).choose_spec)) ?_
  intro arrow morphism
  apply CostructuredArrow.hom_ext
  apply (CochainComplex.IsKInjective.Qh_map_bijective arrow.left I).injective
  simpa using (CostructuredArrow.w morphism).trans (lift arrow).choose_spec.symm

variable {H : Type*} [Category H] (F : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H)
  (RF : DerivedCategory 𝒜 ⥤ H) (unit : F ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))]

/-- A K-injective complex computes any right derived functor on the unbounded homotopy
category. -/
theorem isIso_unit_app_of_isKInjective' (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    IsIso (unit.app ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I)) :=
  isIso_unit_app_of_isKInjective F
    (exists_quasiIso_isKInjective 𝒜) DerivedCategory.Qh RF unit I

/-- Postcomposing a right derived functor with an arbitrary functor again gives a right derived
functor. The pointwise universal property is checked at a K-injective resolution, where the
indexing category of the colimit has a terminal object. -/
theorem isRightDerivedFunctor_postcomp {H' : Type*} [Category H'] (G : H ⥤ H') :
    (RF ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight unit G ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) := by
  let extension := Functor.LeftExtension.mk (RF ⋙ G)
    (Functor.whiskerRight unit G ≫ (Functor.associator _ _ _).hom)
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).2
  apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension (E := extension)
  intro object
  let complex := DerivedCategory.Q.objPreimage object
  let resolution := (Stacks.Injectives.kInjectiveResolutionFunctor 𝒜).obj complex
  let inclusion := (Stacks.Injectives.kInjectiveResolutionInclusion 𝒜).app complex
  let representation := (DerivedCategory.quotientCompQhIso 𝒜).app resolution ≪≫
    (asIso (DerivedCategory.Q.map inclusion)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso object
  apply extension.isPointwiseLeftKanExtensionAtOfIso' _ representation
  let colimitProof := colimitOfDiagramTerminal
    (isTerminalCostructuredArrowOfIsKInjective resolution)
    (CostructuredArrow.proj DerivedCategory.Qh _ ⋙ F ⋙ G)
  have hdesc : colimitProof.desc (extension.coconeAt _) =
      G.map (unit.app ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj resolution)) := by
    simp [colimitProof, colimitOfDiagramTerminal, extension, Functor.LeftExtension.coconeAt]
  have : IsIso (colimitProof.desc (extension.coconeAt _)) := by
    rw [hdesc]
    have := isIso_unit_app_of_isKInjective' F RF unit resolution
    infer_instance
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ colimitProof this

end DerivedGeneralities

/-! ### The bottom degree of a right derived functor -/

section BottomDegree

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- In a distinguished triangle whose third vertex has vanishing cohomology one degree below,
the degree-`n` cohomology sequence of the first two maps is left exact. -/
theorem mono_and_exact_homology_of_distTriang (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (n : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor 𝒜 (n - 1)).obj T.obj₃)) :
    Mono ((DerivedCategory.homologyFunctor 𝒜 n).map T.mor₁) ∧
      (ShortComplex.mk ((DerivedCategory.homologyFunctor 𝒜 n).map T.mor₁)
        ((DerivedCategory.homologyFunctor 𝒜 n).map T.mor₂)
        (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])).Exact := by
  refine ⟨?_, DerivedCategory.HomologySequence.exact₂ T hT n⟩
  rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n (by omega)]
  exact h₀.eq_of_src _ _

variable {ℬ : Type*} [Category ℬ] [Abelian ℬ] [HasDerivedCategory ℬ]

/-- An object of the derived category whose cohomology vanishes below `n` is represented by a
K-injective complex of injectives concentrated in degrees `≥ n`. -/
theorem exists_isKInjective_isStrictlyGE_of_isZero_homology [IsGrothendieckAbelian 𝒜]
    (M : DerivedCategory 𝒜) (n : ℤ)
    (hM : ∀ i : ℤ, i < n → IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj M)) :
    ∃ I : CochainComplex 𝒜 ℤ, I.IsKInjective ∧ I.IsStrictlyGE n ∧ IsZero (I.sc n).X₁ ∧
      Nonempty (DerivedCategory.Q.obj I ≅ M) := by
  have hGE : M.IsGE n := (DerivedCategory.isGE_iff M n).2 hM
  let Mplus : DerivedCategory.Plus 𝒜 := ⟨M, ⟨n, hGE⟩⟩
  have : Mplus.IsGE n := ⟨hGE.ge⟩
  obtain ⟨L, hL, ⟨ePlus⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Mplus n
  have : L.obj.IsStrictlyGE n := hL
  let I : CochainComplex 𝒜 ℤ := ((InjectiveObject.ι 𝒜).mapCochainComplexPlus.obj L).obj
  have hIge : I.IsStrictlyGE n :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := L.obj) (InjectiveObject.ι 𝒜) n).2 hL
  have : ∀ j : ℤ, Injective (I.X j) := fun j => (L.obj.X j).property
  exact ⟨I, CochainComplex.isKInjective_of_injective I n, hIge,
    (CochainComplex.isStrictlyGE_iff I n).1 hIge ((ComplexShape.up ℤ).prev n) (by simp),
    ⟨DerivedCategory.Plus.ι.mapIso ePlus⟩⟩

/-- **The bottom degree of a right derived functor.** For a left exact functor `F` and an object
`M` of the derived category whose cohomology vanishes below `n`, the degree-`n` cohomology of
`RF M` is `F` applied to the degree-`n` cohomology of `M`, and the cohomology of `RF M` vanishes
below `n` as well. The right derived functor is computed on a complex of injectives placed in
degrees `≥ n`, where `F` preserves the homology at `n` because the incoming differential comes
from a zero object. -/
theorem exists_bottomDegreeIso_of_rightDerived [IsGrothendieckAbelian 𝒜]
    (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory 𝒜 ⥤ DerivedCategory ℬ)
    (unit : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    (hunit : ∀ I : CochainComplex 𝒜 ℤ, I.IsKInjective → IsIso (unit.app I))
    (M : DerivedCategory 𝒜) (n : ℤ)
    (hM : ∀ i : ℤ, i < n → IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj M)) :
    ∃ _ : (DerivedCategory.homologyFunctor ℬ n).obj (RF.obj M) ≅
        F.obj ((DerivedCategory.homologyFunctor 𝒜 n).obj M),
      ∀ i : ℤ, i < n → IsZero ((DerivedCategory.homologyFunctor ℬ i).obj (RF.obj M)) := by
  obtain ⟨I, _, hIge, hX₁, ⟨eI⟩⟩ :=
    exists_isKInjective_isStrictlyGE_of_isZero_homology M n hM
  have : IsIso (unit.app I) := hunit I ‹_›
  let eDerived : RF.obj M ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    (RF.mapIso eI).symm ≪≫ (asIso (unit.app I)).symm
  have eH : (DerivedCategory.homologyFunctor ℬ n).obj
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≅
      F.obj ((DerivedCategory.homologyFunctor 𝒜 n).obj M) := by
    have : (I.sc n).leftHomologyData.IsPreservedBy F :=
      { g := inferInstance
        f' := by rw [hX₁.eq_of_src (I.sc n).leftHomologyData.f' 0]; infer_instance }
    have : F.PreservesLeftHomologyOf (I.sc n) :=
      Functor.PreservesLeftHomologyOf.mk' (F := F) (S := I.sc n) (I.sc n).leftHomologyData
    exact (((DerivedCategory.homologyFunctorFactors ℬ n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).trans
      ((I.sc n).mapHomologyIso F)).trans
        (F.mapIso ((DerivedCategory.homologyFunctorFactors 𝒜 n).app I).symm ≪≫
          F.mapIso ((DerivedCategory.homologyFunctor 𝒜 n).mapIso eI))
  refine ⟨((DerivedCategory.homologyFunctor ℬ n).mapIso eDerived).trans eH, fun i hi ↦ ?_⟩
  have : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun j hj => F.map_isZero ((CochainComplex.isStrictlyGE_iff I n).1 hIge j hj)
  have : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).IsGE n :=
    (DerivedCategory.isGE_Q_obj_iff _ n).2 inferInstance
  exact (DerivedCategory.isZero_of_isGE _ n i (by omega)).of_iso
    ((DerivedCategory.homologyFunctor ℬ i).mapIso eDerived)

end BottomDegree

/-! ### Homology of a left exact functor at a short complex with zero first term -/

section PreservedHomology

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {ℬ : Type*} [Category ℬ] [Abelian ℬ]

/-- A left exact functor preserves the homology of a short complex whose first term is zero: the
induced map out of the kernel of the second differential is then zero, hence preserved, and the
two kernels defining the homology are preserved because the functor is left exact. -/
theorem preservesHomologyOf_of_isZero_X₁ (F : 𝒜 ⥤ ℬ) [F.Additive]
    [PreservesFiniteLimits F] (S : ShortComplex 𝒜) (hzero : IsZero S.X₁) :
    F.PreservesLeftHomologyOf S ∧ F.PreservesRightHomologyOf S := by
  have : S.leftHomologyData.IsPreservedBy F :=
    { g := inferInstance
      f' := by rw [hzero.eq_of_src S.leftHomologyData.f' 0]; infer_instance }
  have : S.rightHomologyData.IsPreservedBy F :=
    { f := by rw [hzero.eq_of_src S.f 0]; infer_instance
      g' := inferInstance }
  exact ⟨Functor.PreservesLeftHomologyOf.mk' _ S.leftHomologyData,
    Functor.PreservesRightHomologyOf.mk' _ S.rightHomologyData⟩

/-- The identification of the homology of the image with the image of the homology, for a short
complex with zero first term, is natural in the left exact functor. -/
theorem mapHomologyIso_naturality_of_isZero_X₁ {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (S : ShortComplex 𝒜)
    (hzero : IsZero S.X₁) (τ : F ⟶ G) :
    letI := (preservesHomologyOf_of_isZero_X₁ F S hzero).1
    letI := (preservesHomologyOf_of_isZero_X₁ G S hzero).1
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology := by
  let := (preservesHomologyOf_of_isZero_X₁ F S hzero).1
  let := (preservesHomologyOf_of_isZero_X₁ G S hzero).1
  let := (preservesHomologyOf_of_isZero_X₁ F S hzero).2
  let := (preservesHomologyOf_of_isZero_X₁ G S hzero).2
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PreservedHomology

/-! ### A distinguished triangle of Mayer–Vietoris shape gives a pullback square -/

section PullbackFromTriangle

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- A commutative square in the derived category whose Mayer–Vietoris triangle — the signed
difference of the two restrictions — is distinguished, and whose fourth vertex has vanishing
cohomology one degree below, becomes a pullback square on degree-`n` cohomology. The
cohomology functor preserves the biproduct in the middle, so the left exact cohomology
sequence of the triangle is the short complex of the square. -/
theorem isPullback_map_homologyFunctor_of_distTriang (square : Square (DerivedCategory 𝒜))
    (boundary : square.X₄ ⟶ square.X₁⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk (biprod.lift square.f₁₂ square.f₁₃)
      (biprod.desc square.f₂₄ (-square.f₃₄)) boundary ∈ distTriang (DerivedCategory 𝒜))
    (n : ℤ) (hzero : IsZero ((DerivedCategory.homologyFunctor 𝒜 (n - 1)).obj square.X₄)) :
    (square.map (DerivedCategory.homologyFunctor 𝒜 n)).IsPullback := by
  let homology := DerivedCategory.homologyFunctor 𝒜 n
  have : PreservesBinaryBiproducts homology :=
    preservesBinaryBiproducts_of_preservesBinaryProducts homology
  let triangle := Triangle.mk (biprod.lift square.f₁₂ square.f₁₃)
    (biprod.desc square.f₂₄ (-square.f₃₄)) boundary
  obtain ⟨hmono, hexact⟩ := mono_and_exact_homology_of_distTriang triangle htriangle n hzero
  let source := ShortComplex.mk (homology.map triangle.mor₁) (homology.map triangle.mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ htriangle, Functor.map_zero])
  let target := (square.map homology).commSq.shortComplex'
  let comparison : source ≅ target := ShortComplex.isoMk
    (Iso.refl _) (homology.mapBiprod square.X₂ square.X₃) (Iso.refl _)
    (by simpa [source, target, triangle, homology, Square.map, CommSq.shortComplex'] using
      (biprod.map_lift_mapBiprod homology square.X₂ square.X₃ square.f₁₂ square.f₁₃).symm)
    (by simpa [source, target, triangle, homology, Square.map, CommSq.shortComplex'] using
      biprod.mapBiprod_hom_desc homology square.X₂ square.X₃ square.f₂₄ (-square.f₃₄))
  have htarget : target.Exact := ShortComplex.exact_of_iso comparison hexact
  have : Mono target.f := by
    have : Mono source.f := hmono
    have hcomp : Mono (source.f ≫ comparison.hom.τ₂) := inferInstance
    have heq : source.f ≫ comparison.hom.τ₂ = target.f := by
      have hcomm := comparison.hom.comm₁₂
      change (𝟙 target.X₁) ≫ target.f = source.f ≫ comparison.hom.τ₂ at hcomm
      rw [Category.id_comp] at hcomm
      exact hcomm.symm
    rw [← heq]
    exact hcomp
  exact (square.map homology).isPullbackEquivIsLimitKernelFork.symm htarget.fIsKernel

end PullbackFromTriangle

/-! ### Detecting a finer topology on a sheaf in an arbitrary universe -/

section DescentWitnesses

variable {C : Type u} [Category.{w} C]

/-- The syntax of the three ways a section of a presheaf can be manufactured from a prescribed
family of sections: restriction along a morphism of the site, amalgamation of a compatible
family along a covering, and the amalgamation of two sections over the two middle vertices of
one of the given squares.

This is used to generate, inside a sheaf of sets in an arbitrary universe, a subfunctor small
enough to be fed to a detection hypothesis stated in one fixed universe. -/
private inductive DescentWitness (J : GrothendieckTopology C) (squares : Set (Square C))
    (generators : C → Type max u w) : C → Type max u w
  | base (object : C) : generators object → DescentWitness J squares generators object
  | restrict {source target : C} (restriction : source ⟶ target) :
      DescentWitness J squares generators target → DescentWitness J squares generators source
  | amalgamate {object : C} (cover : Sieve object) (hcover : cover ∈ J object)
      (family : ∀ ⦃source : C⦄ (restriction : source ⟶ object), cover restriction →
        DescentWitness J squares generators source) :
      DescentWitness J squares generators object
  | square (diagram : Square C) (hdiagram : diagram ∈ squares)
      (first : DescentWitness J squares generators diagram.X₂)
      (second : DescentWitness J squares generators diagram.X₃) :
      DescentWitness J squares generators diagram.X₄

variable {J : GrothendieckTopology C} {squares : Set (Square C)}

open scoped Classical in
/-- The section of the presheaf a witness denotes, if the witness is coherent: amalgamation
produces a section only when the family it is applied to is itself coherent and compatible, and
the square constructor only when the two sections agree on the first vertex. -/
private def DescentWitness.evaluate {generators : C → Type max u w} (presheaf : Cᵒᵖ ⥤ Type v)
    (hsheaf : Presieve.IsSheaf J presheaf)
    (hsquares : ∀ diagram ∈ squares, (diagram.op.map presheaf).IsPullback)
    (sections : ∀ object, generators object → presheaf.obj (op object)) :
    {object : C} → DescentWitness J squares generators object →
      Option (presheaf.obj (op object))
  | _, .base object generator => some (sections object generator)
  | _, .restrict restriction witness =>
      (evaluate presheaf hsheaf hsquares sections witness).map (presheaf.map restriction.op)
  | _, .amalgamate cover hcover family =>
      let values := fun source (restriction : source ⟶ _) (hrestriction : cover restriction) ↦
        evaluate presheaf hsheaf hsquares sections (family restriction hrestriction)
      if hall : ∀ source (restriction : source ⟶ _) (hrestriction : cover restriction),
          (values source restriction hrestriction).isSome then
        let family' : cover.arrows.FamilyOfElements presheaf :=
          fun source restriction hrestriction ↦
            (values source restriction hrestriction).get (hall source restriction hrestriction)
        if hcompatible : family'.Compatible then
          some ((hsheaf cover hcover family' hcompatible).choose)
        else none
      else none
  | _, .square diagram hdiagram first second => do
      let firstSection ← evaluate presheaf hsheaf hsquares sections first
      let secondSection ← evaluate presheaf hsheaf hsquares sections second
      if hcompatible : presheaf.map diagram.f₁₂.op firstSection =
          presheaf.map diagram.f₁₃.op secondSection then
        some ((Types.exists_of_isPullback (hsquares diagram hdiagram)
          firstSection secondSection hcompatible).choose)
      else none

variable (J squares) in
/-- The subfunctor of sections denoted by some coherent witness: the smallest subfunctor
containing the prescribed sections and closed under restriction, under amalgamation along
`J`-coverings, and under the pullback property of the given squares. -/
private def descentSubfunctor (presheaf : Cᵒᵖ ⥤ Type v)
    (hsheaf : Presieve.IsSheaf J presheaf)
    (hsquares : ∀ diagram ∈ squares, (diagram.op.map presheaf).IsPullback)
    (generators : C → Type max u w)
    (sections : ∀ object, generators object → presheaf.obj (op object)) :
    Subfunctor presheaf where
  obj object := {element | ∃ witness : DescentWitness J squares generators object.unop,
    witness.evaluate presheaf hsheaf hsquares sections = some element}
  map restriction := by
    rintro element ⟨witness, hwitness⟩
    exact ⟨.restrict restriction.unop witness, by
      simp [DescentWitness.evaluate, hwitness]⟩

variable {presheaf : Cᵒᵖ ⥤ Type v} (hsheaf : Presieve.IsSheaf J presheaf)
  (hsquares : ∀ diagram ∈ squares, (diagram.op.map presheaf).IsPullback)
  (generators : C → Type max u w)
  (sections : ∀ object, generators object → presheaf.obj (op object))

/-- The generated subfunctor is small in the universe the witnesses live in: every one of its
sections is denoted by a witness, and the witness determines the section. -/
private theorem descentSubfunctor_small (object : C) :
    Small.{max u w}
      ((descentSubfunctor J squares presheaf hsheaf hsquares generators sections).obj
        (op object)) := by
  let sub := descentSubfunctor J squares presheaf hsheaf hsquares generators sections
  choose witness hwitness using fun element : sub.obj (op object) ↦ element.property
  exact small_of_injective (f := witness) (by
    intro first second hequal
    apply Subtype.ext
    apply Option.some_injective
    rw [← hwitness first, ← hwitness second, hequal])

/-- The generated subfunctor is a `J`-sheaf: it is separated because it is a subfunctor of one,
and a compatible family of its sections is amalgamated inside it by the amalgamation
constructor. -/
private theorem descentSubfunctor_isSheaf :
    Presieve.IsSheaf J
      (descentSubfunctor J squares presheaf hsheaf hsquares generators sections).toFunctor := by
  classical
  let sub := descentSubfunctor J squares presheaf hsheaf hsquares generators sections
  intro object cover hcover
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono sub.ι (hsheaf cover hcover).isSeparatedFor, ?_⟩
  intro family hcompatible
  let family' := family.map sub.ι
  have hcompatible' : family'.Compatible := hcompatible.map sub.ι
  obtain ⟨element, hsection, hunique⟩ := hsheaf cover hcover family' hcompatible'
  have hmem : element ∈ sub.obj (op object) := by
    choose witness hwitness using fun source (restriction : source ⟶ object)
      (hrestriction : cover restriction) ↦ (family restriction hrestriction).property
    refine ⟨.amalgamate cover hcover
      (fun {source} restriction hrestriction ↦ witness source restriction hrestriction), ?_⟩
    simp only [DescentWitness.evaluate, hwitness, Option.isSome_some, implies_true,
      dite_true, Option.get_some]
    change (if h : family'.Compatible then some ((hsheaf cover hcover family' h).choose)
      else none) = some element
    rw [dite_eq_left hcompatible']
    exact congrArg some (hunique _ (hsheaf cover hcover family' hcompatible').choose_spec.1)
  exact ⟨⟨element, hmem⟩, .of_mono sub.ι hsection⟩

/-- The generated subfunctor inherits the pullback property at each of the given squares: the
fourth-vertex section produced by the ambient pullback property is denoted by the square
constructor. -/
private theorem descentSubfunctor_isPullback (diagram : Square C) (hdiagram : diagram ∈ squares) :
    (diagram.op.map
      (descentSubfunctor J squares presheaf hsheaf hsquares generators
        sections).toFunctor).IsPullback := by
  classical
  let sub := descentSubfunctor J squares presheaf hsheaf hsquares generators sections
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨(diagram.op.map sub.toFunctor).fac, ?_, ?_⟩
  · intro first second hequal
    apply Subtype.ext
    exact Types.ext_of_isPullback (hsquares diagram hdiagram)
      (congrArg Subtype.val hequal.1) (congrArg Subtype.val hequal.2)
  · intro first second hcompatible
    have hcompatible' : presheaf.map diagram.f₁₂.op first.val =
        presheaf.map diagram.f₁₃.op second.val := congrArg Subtype.val hcompatible
    obtain ⟨element, hfirst, hsecond⟩ :=
      Types.exists_of_isPullback (hsquares diagram hdiagram) first.val second.val hcompatible'
    obtain ⟨firstWitness, hfirstWitness⟩ := first.property
    obtain ⟨secondWitness, hsecondWitness⟩ := second.property
    have hmem : element ∈ sub.obj (op diagram.X₄) := by
      refine ⟨.square diagram hdiagram firstWitness secondWitness, ?_⟩
      simp only [DescentWitness.evaluate]
      rw [show DescentWitness.evaluate (object := diagram.X₂) presheaf hsheaf hsquares
            sections firstWitness = some first.val from hfirstWitness,
        show DescentWitness.evaluate (object := diagram.X₃) presheaf hsheaf hsquares
            sections secondWitness = some second.val from hsecondWitness]
      change (if h : presheaf.map diagram.f₁₂.op first.val =
          presheaf.map diagram.f₁₃.op second.val then
        some ((Types.exists_of_isPullback (hsquares diagram hdiagram)
          first.val second.val h).choose) else none) = some element
      rw [dite_eq_left hcompatible']
      exact congrArg some <| Types.ext_of_isPullback (hsquares diagram hdiagram)
        ((Types.exists_of_isPullback (hsquares diagram hdiagram) first.val second.val
          hcompatible').choose_spec.1.trans hfirst.symm)
        ((Types.exists_of_isPullback (hsquares diagram hdiagram) first.val second.val
          hcompatible').choose_spec.2.trans hsecond.symm)
    exact ⟨⟨element, hmem⟩, Subtype.ext hfirst, Subtype.ext hsecond⟩

/-- Shrinking a presheaf of sets to a smaller universe preserves the pullback property at a
square. -/
private theorem isPullback_map_shrink (diagram : Square C)
    (presheaf : Cᵒᵖ ⥤ Type v) [FunctorToTypes.Small.{max u w} presheaf]
    (hpullback : (diagram.op.map presheaf).IsPullback) :
    (diagram.op.map (FunctorToTypes.shrink.{max u w} presheaf)).IsPullback := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨(diagram.op.map (FunctorToTypes.shrink presheaf)).fac, ?_, ?_⟩
  · intro first second hequal
    exact (equivShrink (presheaf.obj (op diagram.X₄))).symm.injective
      (Types.ext_of_isPullback hpullback
        ((equivShrink (presheaf.obj (op diagram.X₂))).injective hequal.1)
        ((equivShrink (presheaf.obj (op diagram.X₃))).injective hequal.2))
  · intro first second hcompatible
    obtain ⟨element, hfirst, hsecond⟩ := Types.exists_of_isPullback hpullback
      ((equivShrink (presheaf.obj (op diagram.X₂))).symm first)
      ((equivShrink (presheaf.obj (op diagram.X₃))).symm second)
      ((equivShrink (presheaf.obj (op diagram.X₁))).injective hcompatible)
    refine ⟨equivShrink (presheaf.obj (op diagram.X₄)) element, ?_, ?_⟩
    · exact (congrArg (equivShrink (presheaf.obj (op diagram.X₂)))
        ((congrArg (fun x ↦ (presheaf.map diagram.f₂₄.op) x)
          ((equivShrink (presheaf.obj (op diagram.X₄))).symm_apply_apply element)).trans
            hfirst)).trans
        ((equivShrink (presheaf.obj (op diagram.X₂))).apply_symm_apply first)
    · exact (congrArg (equivShrink (presheaf.obj (op diagram.X₃)))
        ((congrArg (fun x ↦ (presheaf.map diagram.f₃₄.op) x)
          ((equivShrink (presheaf.obj (op diagram.X₄))).symm_apply_apply element)).trans
            hsecond)).trans
        ((equivShrink (presheaf.obj (op diagram.X₃))).apply_symm_apply second)

variable (J) in
/-- A detection hypothesis stated for `J'`-sheaves of sets in `Type max u w` applies to the
subfunctor generated inside a `J'`-sheaf of sets in an arbitrary universe, after shrinking it to
`Type max u w`. -/
private theorem isSheaf_descentSubfunctor {J' : GrothendieckTopology C}
    (hdescent : ∀ F : Sheaf J' (Type max u w),
      (∀ diagram ∈ squares, (diagram.op.map F.obj).IsPullback) → Presheaf.IsSheaf J F.obj)
    (hsheaf : Presieve.IsSheaf J' presheaf)
    (hsquares : ∀ diagram ∈ squares, (diagram.op.map presheaf).IsPullback) :
    Presieve.IsSheaf J
      (descentSubfunctor J' squares presheaf hsheaf hsquares generators sections).toFunctor := by
  let sub := descentSubfunctor J' squares presheaf hsheaf hsquares generators sections
  have : FunctorToTypes.Small.{max u w} sub.toFunctor := fun object ↦
    descentSubfunctor_small hsheaf hsquares generators sections object.unop
  let shrunk := FunctorToTypes.shrink sub.toFunctor
  have hnatural : ∀ {source target : C} (restriction : source ⟶ target)
      (element : sub.toFunctor.obj (op target)),
      equivShrink.{max u w} _ (sub.toFunctor.map restriction.op element) =
        shrunk.map restriction.op (equivShrink.{max u w} _ element) := by
    intros
    simp [shrunk, FunctorToTypes.shrink]
  have hshrunk : Presieve.IsSheaf J' shrunk :=
    Presieve.isSheaf_of_nat_equiv (fun {_} ↦ equivShrink.{max u w} _)
      (fun {_ _} restriction element ↦ hnatural restriction element)
      (descentSubfunctor_isSheaf hsheaf hsquares generators sections)
  have hresult := hdescent ⟨shrunk, (isSheaf_iff_isSheaf_of_type _ _).2 hshrunk⟩
    (fun diagram hdiagram ↦ isPullback_map_shrink diagram sub.toFunctor
      (descentSubfunctor_isPullback hsheaf hsquares generators sections diagram hdiagram))
  exact (Presieve.isSheaf_iff_of_nat_equiv (fun {_} ↦ equivShrink.{max u w} _)
    (fun {_ _} restriction element ↦ hnatural restriction element)).2
      ((isSheaf_iff_isSheaf_of_type _ _).1 hresult)

variable (J squares) in
/-- **A family of squares that detects `J`-sheaves among `J'`-sheaves of sets in `Type max u w`
detects them in every universe.** Both halves of the `J`-sheaf condition are obtained by
applying the hypothesis to the subfunctor generated by the sections the condition speaks of:
separatedness to the one generated by the given family together with the two candidate
amalgamations, and existence of an amalgamation to the one generated by the family alone. -/
theorem isSheaf_of_forall_isPullback {J' : GrothendieckTopology C}
    (hdescent : ∀ F : Sheaf J' (Type max u w),
      (∀ diagram ∈ squares, (diagram.op.map F.obj).IsPullback) → Presheaf.IsSheaf J F.obj)
    (presheaf : Cᵒᵖ ⥤ Type v) (hsheaf : Presieve.IsSheaf J' presheaf)
    (hsquares : ∀ diagram ∈ squares, (diagram.op.map presheaf).IsPullback) :
    Presieve.IsSheaf J presheaf := by
  classical
  intro object cover hcover
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro family first second hfirst hsecond
    let generators (source : C) : Type max u w :=
      ULift.{u} ({restriction : source ⟶ object // cover restriction} ⊕
        ((source ⟶ object) ⊕ (source ⟶ object)))
    let sections (source : C) : generators source → presheaf.obj (op source) :=
      fun generator ↦ match generator.down with
        | .inl restriction => family restriction.val restriction.property
        | .inr (.inl restriction) => presheaf.map restriction.op first
        | .inr (.inr restriction) => presheaf.map restriction.op second
    let sub := descentSubfunctor J' squares presheaf hsheaf hsquares generators sections
    have hsub := isSheaf_descentSubfunctor J generators sections hdescent hsheaf hsquares
    let subfamily : cover.arrows.FamilyOfElements sub.toFunctor :=
      fun source restriction hrestriction ↦
        ⟨family restriction hrestriction, ⟨.base source ⟨.inl ⟨restriction, hrestriction⟩⟩, rfl⟩⟩
    have hmemFirst : first ∈ sub.obj (op object) :=
      ⟨.base object ⟨.inr (.inl (𝟙 object))⟩, by simp [DescentWitness.evaluate, sections]⟩
    have hmemSecond : second ∈ sub.obj (op object) :=
      ⟨.base object ⟨.inr (.inr (𝟙 object))⟩, by simp [DescentWitness.evaluate, sections]⟩
    have hequal : (⟨first, hmemFirst⟩ : sub.obj _) = ⟨second, hmemSecond⟩ :=
      (hsub cover hcover).isSeparatedFor subfamily _ _
        (.of_mono sub.ι hfirst) (.of_mono sub.ι hsecond)
    exact congrArg Subtype.val hequal
  · intro family hcompatible
    let generators (source : C) : Type max u w :=
      ULift.{u} {restriction : source ⟶ object // cover restriction}
    let sections (source : C) : generators source → presheaf.obj (op source) :=
      fun generator ↦ family generator.down.val generator.down.property
    let sub := descentSubfunctor J' squares presheaf hsheaf hsquares generators sections
    have hsub := isSheaf_descentSubfunctor J generators sections hdescent hsheaf hsquares
    let subfamily : cover.arrows.FamilyOfElements sub.toFunctor :=
      fun source restriction hrestriction ↦
        ⟨family restriction hrestriction, ⟨.base source ⟨⟨restriction, hrestriction⟩⟩, rfl⟩⟩
    obtain ⟨element, helement, hunique⟩ := hsub cover hcover subfamily
      (.of_mono sub.ι hcompatible)
    exact ⟨element.val, helement.map sub.ι⟩

end DescentWitnesses

/-! ### Adjunctions between induced functors on homotopy and derived categories -/

section InducedAdjunctions

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟]

/-- An adjunction between additive functors induces an adjunction between the induced functors
on homotopy categories. The unit and counit are degreewise those of the given adjunction; both
triangle identities hold already on complexes, hence after passing to homotopy classes. -/
def mapHomotopyCategoryAdjunction {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} [F.Additive] [G.Additive]
    (adj : G ⊣ F) (c : ComplexShape ℤ) :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c := by
  let adjC : G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c :=
    { unit :=
        { app := fun X => { f := fun n => adj.unit.app (X.X n), comm' := fun _ _ _ => by simp }
          naturality := fun X Y f => by ext n; simp }
      counit :=
        { app := fun Y => { f := fun n => adj.counit.app (Y.X n), comm' := fun _ _ _ => by simp }
          naturality := fun X Y f => by ext n; simp }
      left_triangle_components := by intro X; ext n; simp
      right_triangle_components := by intro Y; ext n; simp }
  refine
    { unit := Quotient.natTransLift _ (Functor.whiskerRight adjC.unit
        (HomotopyCategory.quotient 𝒟 c)),
      counit := Quotient.natTransLift _ (Functor.whiskerRight adjC.counit
        (HomotopyCategory.quotient 𝒞 c)),
      left_triangle_components := ?_,
      right_triangle_components := ?_ }
  · rintro ⟨X⟩
    exact ((HomotopyCategory.quotient 𝒞 c).map_comp _ _).symm.trans
      ((congrArg _ (adjC.left_triangle_components X)).trans
        ((HomotopyCategory.quotient 𝒞 c).map_id _))
  · rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient 𝒟 c).map_comp _ _).symm.trans
      ((congrArg _ (adjC.right_triangle_components Y)).trans
        ((HomotopyCategory.quotient 𝒟 c).map_id _))

end InducedAdjunctions

section DerivedAdjunction

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞] [IsGrothendieckAbelian 𝒞]
  {𝒟 : Type*} [Category 𝒟] [Abelian 𝒟] [HasDerivedCategory 𝒟]
  (L : 𝒟 ⥤ 𝒞) (R : 𝒞 ⥤ 𝒟) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  (RR : DerivedCategory 𝒞 ⥤ DerivedCategory 𝒟)
  (unit : R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RR)
  [RR.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ))]

/-- **The derived adjunction.** For an exact left adjoint `L` with right adjoint `R`, the induced
functor `L.mapDerivedCategory` is left adjoint to any right derived functor of `R`. The left-hand
side is its own left derived functor, because an exact functor inverts quasi-isomorphisms, and
both composites are again derived functors, so `Adjunction.derived` applies. -/
def mapDerivedCategoryAdjunction : L.mapDerivedCategory ⊣ RR := by
  let Wc := HomotopyCategory.quasiIso 𝒟 (ComplexShape.up ℤ)
  let Wd := HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ)
  let adjH := mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)
  let α := L.mapDerivedCategoryFactorsh.hom
  let _ : L.mapDerivedCategory.IsLeftDerivedFunctor α Wc :=
    Functor.isLeftDerivedFunctor_of_inverts Wc L.mapDerivedCategory L.mapDerivedCategoryFactorsh
  have hL : Wc.IsInvertedBy
      (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _ L.mapDerivedCategoryFactorsh.symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh (Localization.inverts _ _) _
  let _ : RR.IsLeftKanExtension unit :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension RR unit Wd
  let _ : (L.mapDerivedCategory ⋙ RR).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh L.mapDerivedCategory RR).inv ≫
        Functor.whiskerRight α RR) Wc := by
    apply (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
      (MorphismProperty.IsInvertedBy.of_comp _ _ hL RR)).2
    infer_instance
  have := isRightDerivedFunctor_postcomp
    (R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RR unit
    L.mapDerivedCategory
  exact adjH.derived Wc Wd α unit

/-- **The derived right adjoint of a fully faithful right adjoint is fully faithful**, which is
how `ε^{-1} R ε_* = id` is expressed. The counit of the underlying adjunction is invertible, so
the composite `R.mapHomotopyCategory ⋙ Qh ⋙ L.mapDerivedCategory` inverts quasi-isomorphisms;
being a right derived functor of itself, its comparison with `RR ⋙ L.mapDerivedCategory` is
invertible, which exhibits `RR ⋙ L.mapDerivedCategory ≅ 𝟭`. -/
def fullyFaithfulOfDerivedAdjunction [R.Full] [R.Faithful]
    (derivedAdj : L.mapDerivedCategory ⊣ RR) : RR.FullyFaithful := by
  let homotopyR := R.mapHomotopyCategory (ComplexShape.up ℤ)
  let homotopyL := L.mapHomotopyCategory (ComplexShape.up ℤ)
  let homotopyAdj := mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)
  let comparison : homotopyR ⋙ DerivedCategory.Qh ⋙ L.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ RR ⋙ L.mapDerivedCategory :=
    Functor.whiskerRight unit L.mapDerivedCategory ≫ (Functor.associator _ _ _).hom
  have _ : (RR ⋙ L.mapDerivedCategory).IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ)) :=
    isRightDerivedFunctor_postcomp (homotopyR ⋙ DerivedCategory.Qh) RR unit
      L.mapDerivedCategory
  let computation : homotopyR ⋙ DerivedCategory.Qh ⋙ L.mapDerivedCategory ≅
      DerivedCategory.Qh :=
    Functor.isoWhiskerLeft homotopyR L.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator homotopyR homotopyL DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight (asIso homotopyAdj.counit) DerivedCategory.Qh ≪≫
      Functor.leftUnitor DerivedCategory.Qh
  have hinverts : (HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ)).IsInvertedBy
      (homotopyR ⋙ DerivedCategory.Qh ⋙ L.mapDerivedCategory) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _ computation]
    exact Localization.inverts _ _
  have _ : IsIso comparison := Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (RR ⋙ L.mapDerivedCategory) comparison hinverts
  let identityComparison : DerivedCategory.Qh ⋙ RR ⋙ L.mapDerivedCategory ≅
      DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory 𝒞) :=
    (asIso comparison).symm ≪≫ computation ≪≫ (Functor.rightUnitor DerivedCategory.Qh).symm
  exact derivedAdj.fullyFaithfulROfCompIsoId
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
      (HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ)) _).preimageIso identityComparison)

end DerivedAdjunction

section PreservesIsGE

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞] [IsGrothendieckAbelian 𝒞]
  {𝒟 : Type*} [Category 𝒟] [Abelian 𝒟] [HasDerivedCategory 𝒟]

/-- **A right derived functor of a left exact functor preserves boundedness below.** This is the
vanishing half of `exists_bottomDegreeIso_of_rightDerived`, transported from the unit on
complexes to the unit on the homotopy category. -/
theorem isGE_rightDerived_obj (F : 𝒞 ⥤ 𝒟) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory 𝒞 ⥤ DerivedCategory 𝒟)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso 𝒞 (ComplexShape.up ℤ))]
    (M : DerivedCategory 𝒞) (n : ℤ) (hM : M.IsGE n) : (RF.obj M).IsGE n := by
  let quotient := HomotopyCategory.quotient 𝒞 (ComplexShape.up ℤ)
  let sourceComparison : quotient ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomologicalComplexUpToQuasiIso.quotientCompQhIso 𝒟 (ComplexShape.up ℤ))
  let targetComparison : quotient ⋙ (DerivedCategory.Qh ⋙ RF) ≅ DerivedCategory.Q ⋙ RF :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomologicalComplexUpToQuasiIso.quotientCompQhIso 𝒞 (ComplexShape.up ℤ)) RF
  let comparison : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
    sourceComparison.inv ≫ Functor.whiskerLeft quotient unit ≫ targetComparison.hom
  obtain ⟨-, hlower⟩ := exists_bottomDegreeIso_of_rightDerived F RF comparison
    (fun I hI => by
      have := hI
      have := isIso_unit_app_of_isKInjective'
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RF unit I
      simp only [comparison, NatTrans.comp_app, Functor.whiskerLeft_app]
      infer_instance)
    M n ((DerivedCategory.isGE_iff M n).1 hM)
  exact (DerivedCategory.isGE_iff _ n).2 hlower

end PreservesIsGE

/-! ### Sections of the lowest cohomology sheaf over a square -/

section Site

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}}
  [HasSheafify S.J AddCommGrpCat.{v}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- Taking sections of a sheaf of modules over an object of the site is additive. -/
private local instance sections_additive (U : S.C) :
    (sections.{u, v, w, r} S U).Additive where
  map_add := rfl

/-- Taking sections of a sheaf of modules over an object of the site is left exact: it is the
forgetful functor to presheaves of abelian groups, which is a right adjoint, followed by
evaluation at that object. -/
private local instance sections_preservesFiniteLimits (U : S.C) :
    PreservesFiniteLimits (sections.{u, v, w, r} S U) := by
  change PreservesFiniteLimits
    ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) ⋙ sheafToPresheaf S.J AddCommGrpCat.{v}) ⋙
      (evaluation _ _).obj (op U))
  infer_instance

/-- **The sections of the lowest cohomology sheaf over a square form a pullback square.** Let `K`
be an object of `D(𝒪)` whose cohomology vanishes below the degree `n`, and let the canonical
comparison map of [Stacks, Tag 0F16] for a commutative square `E ⟶ Y`, `Z ⟶ X` be invertible at
`K`. Then

```
Γ(X, Hⁿ K) ⟶ Γ(Y, Hⁿ K)
    ↓             ↓
Γ(Z, Hⁿ K) ⟶ Γ(E, Hⁿ K)
```

is a pullback square of abelian groups.

The canonical triangle of [Stacks, Tag 0F16] on derived sections is distinguished, and derived
sections over the first vertex have no cohomology below `n`, so its degree-`n` cohomology
sequence is left exact; and in that degree derived sections agree with ordinary sections of the
degree-`n` cohomology sheaf, because `K` is represented by a complex of injectives in degrees
`≥ n`, on which ordinary sections preserve the homology at `n`. -/
theorem isPullback_sections_homology (sq : Square S.C)
    (K : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))) (n : ℤ)
    (hvanish : ∀ i : ℤ, i < n →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{v}
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) i).obj K))
    (hsquare : (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).IsCSquareIso K) :
    (sq.op.map ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{v}
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) n).obj K)).obj).IsPullback
      := by
  let modules := SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  let homology := DerivedCategory.homologyFunctor AddCommGrpCat.{v} n
  let data := (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).sectionsData
  obtain ⟨complex, _, -, hzero, ⟨isoComplex⟩⟩ :=
    exists_isKInjective_isStrictlyGE_of_isZero_homology K n hvanish
  let ordinary (U : S.Cᵒᵖ) := sections.{u, v, w, r} S U.unop
  have hleft (U : S.Cᵒᵖ) : (ordinary U).PreservesLeftHomologyOf (complex.sc n) :=
    (preservesHomologyOf_of_isZero_X₁ (ordinary U) (complex.sc n) hzero).1
  have hright (U : S.Cᵒᵖ) : (ordinary U).PreservesRightHomologyOf (complex.sc n) :=
    (preservesHomologyOf_of_isZero_X₁ (ordinary U) (complex.sc n) hzero).2
  have := hleft
  have := hright
  let factorsAb := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n
  let factorsMod := DerivedCategory.homologyFunctorFactors modules n
  let tailIso : (complex.sc n).homology ≅ (DerivedCategory.homologyFunctor modules n).obj K :=
    (factorsMod.app complex).symm ≪≫
      (DerivedCategory.homologyFunctor modules n).mapIso isoComplex
  let comparison (U : S.Cᵒᵖ) :
      homology.obj ((data.functor.obj U).obj K) ⟶
        (sections.{u, v, w, r} S U.unop).obj
          ((DerivedCategory.homologyFunctor modules n).obj K) :=
    homology.map ((data.functor.obj U).map isoComplex.inv) ≫
      homology.map (inv ((data.unit U.unop).app complex)) ≫
      factorsAb.hom.app ((sectionsComplex.{u, v, w, r} S U.unop).obj complex) ≫
      ((complex.sc n).mapHomologyIso (sections.{u, v, w, r} S U.unop)).hom ≫
      (sections.{u, v, w, r} S U.unop).map tailIso.hom
  let comparisonIso (U : S.Cᵒᵖ) :
      homology.obj ((data.functor.obj U).obj K) ≅
        (sections.{u, v, w, r} S U.unop).obj
          ((DerivedCategory.homologyFunctor modules n).obj K) :=
    homology.mapIso ((data.functor.obj U).mapIso isoComplex).symm ≪≫
      homology.mapIso (asIso ((data.unit U.unop).app complex)).symm ≪≫
      factorsAb.app ((sectionsComplex.{u, v, w, r} S U.unop).obj complex) ≪≫
      (complex.sc n).mapHomologyIso (sections.{u, v, w, r} S U.unop) ≪≫
      (sections.{u, v, w, r} S U.unop).mapIso tailIso
  have hcomparisonIso (U : S.Cᵒᵖ) : (comparisonIso U).hom = comparison U := rfl
  have hnatural {U V : S.Cᵒᵖ} (restriction : U ⟶ V) :
      homology.map ((data.functor.map restriction).app K) ≫ comparison V =
        comparison U ≫
          (sectionsRestriction.{u, v, w, r} S restriction.unop).app
            ((DerivedCategory.homologyFunctor modules n).obj K) := by
    have hunit : (data.functor.map restriction).app (DerivedCategory.Q.obj complex) ≫
        inv ((data.unit V.unop).app complex) =
      inv ((data.unit U.unop).app complex) ≫
        DerivedCategory.Q.map
          ((sectionsRestrictionComplex.{u, v, w, r} S restriction.unop).app complex) := by
      apply (cancel_mono ((data.unit V.unop).app complex)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [data.unit_restriction]
      simp
    have hfactor := factorsAb.hom.naturality
      ((sectionsRestrictionComplex.{u, v, w, r} S restriction.unop).app complex)
    have hbase :
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
            ((sectionsRestrictionComplex.{u, v, w, r} S restriction.unop).app complex) ≫
            ((complex.sc n).mapHomologyIso (sections.{u, v, w, r} S V.unop)).hom =
          ((complex.sc n).mapHomologyIso (sections.{u, v, w, r} S U.unop)).hom ≫
            (sectionsRestriction.{u, v, w, r} S restriction.unop).app (complex.sc n).homology :=
      mapHomologyIso_naturality_of_isZero_X₁ (complex.sc n) hzero
        (sectionsRestriction.{u, v, w, r} S restriction.unop)
    have hhomology {X : AddCommGrpCat.{v}}
        (x : (sections.{u, v, w, r} S V.unop).obj (complex.sc n).homology ⟶ X) :
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
            ((sectionsRestrictionComplex.{u, v, w, r} S restriction.unop).app complex) ≫
            ((complex.sc n).mapHomologyIso (sections.{u, v, w, r} S V.unop)).hom ≫ x =
          ((complex.sc n).mapHomologyIso (sections.{u, v, w, r} S U.unop)).hom ≫
            (sectionsRestriction.{u, v, w, r} S restriction.unop).app
              (complex.sc n).homology ≫ x :=
      (Category.assoc _ _ x).symm.trans
        ((congrArg (fun y ↦ y ≫ x) hbase).trans (Category.assoc _ _ x))
    have hrestriction :=
      (sectionsRestriction.{u, v, w, r} S restriction.unop).naturality tailIso.hom
    have hderived := congrArg homology.map
      ((data.functor.map restriction).naturality isoComplex.inv).symm
    have hunitHomology := congrArg homology.map hunit
    simp only [Functor.map_comp] at hderived hunitHomology
    dsimp only [comparison]
    simp only [Category.assoc] at *
    rw [reassoc_of% hderived, reassoc_of% hunitHomology, reassoc_of% hfactor, hhomology,
      hrestriction]
  let presheaf := data.functor ⋙ (evaluation _ _).obj K
  let sectionIso : presheaf ⋙ homology ≅
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).obj
        ((DerivedCategory.homologyFunctor modules n).obj K)).obj :=
    NatIso.ofComponents comparisonIso (fun restriction ↦ by
      simp only [hcomparisonIso]
      exact hnatural restriction)
  have : (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).IsCSquareIso K := hsquare
  have htriangle :=
    CanonicalMapOfComplexes.cSquareTriangle_distinguished.{u, v} (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq K
  obtain ⟨-, hbottom⟩ := exists_bottomDegreeIso_of_rightDerived
    (sections.{u, v, w, r} S sq.X₁) (data.functor.obj (op sq.X₁)) (data.unit sq.X₁)
    (fun I _ ↦ data.isIso_unit_app sq.X₁ I)
    K n hvanish
  have hpullback := isPullback_map_homologyFunctor_of_distTriang (sq.op.map presheaf).flip
    (((CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).cSquareTriangle K).mor₃)
    (by convert htriangle using 1; rfl)
    n (hbottom (n - 1) (by omega))
  exact hpullback.flip.of_iso ((Square.mapFunctor.flip.obj sq.op).mapIso sectionIso)

end Site

/-! ### Sections of the lowest cohomology object over a square, for a system of section functors -/

section GeneralSystem

variable {ι : Type*} [Category* ι] {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
  {ℬ : Type*} [Category* ℬ] [Abelian ℬ]
  (S : ιᵒᵖ ⥤ (𝒜 ⥤ ℬ)) [∀ X : ιᵒᵖ, (S.obj X).Additive]
  [∀ X : ιᵒᵖ, PreservesFiniteLimits (S.obj X)]

/-- **The sections of the lowest cohomology object over a square form a pullback square**, for
an arbitrary contravariant system `S` of additive left exact section functors on a Grothendieck
abelian category. Let `K` be an object of `D(𝒜)` whose cohomology vanishes below the degree
`n`, and let the canonical comparison map of [Stacks, Tag 0F16] for a commutative square be
invertible at `K`. Then the sections of `Hⁿ K` over the square form a pullback square.

This is `isPullback_sections_homology` with the sections of a sheaf of modules replaced by the
section functors of `S`; the proof is the same. -/
theorem General.isPullback_sections_homology [IsGrothendieckAbelian.{v} 𝒜] (sq : Square ι)
    (D : CanonicalMapOfComplexes.General.DerivedCSquareData S sq)
    (K : DerivedCategory 𝒜) (n : ℤ)
    (hvanish : ∀ i : ℤ, i < n → IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K))
    (hsquare : D.IsCSquareIso K) :
    (sq.op.map (S.flip.obj ((DerivedCategory.homologyFunctor 𝒜 n).obj K))).IsPullback := by
  let homology := DerivedCategory.homologyFunctor ℬ n
  let data := D.sectionsData
  obtain ⟨complex, _, -, hzero, ⟨isoComplex⟩⟩ :=
    exists_isKInjective_isStrictlyGE_of_isZero_homology K n hvanish
  have hleft (U : ιᵒᵖ) : (S.obj U).PreservesLeftHomologyOf (complex.sc n) :=
    (preservesHomologyOf_of_isZero_X₁ (S.obj U) (complex.sc n) hzero).1
  have hright (U : ιᵒᵖ) : (S.obj U).PreservesRightHomologyOf (complex.sc n) :=
    (preservesHomologyOf_of_isZero_X₁ (S.obj U) (complex.sc n) hzero).2
  have := hleft
  have := hright
  let factorsB := DerivedCategory.homologyFunctorFactors ℬ n
  let factorsA := DerivedCategory.homologyFunctorFactors 𝒜 n
  let tailIso : (complex.sc n).homology ≅ (DerivedCategory.homologyFunctor 𝒜 n).obj K :=
    (factorsA.app complex).symm ≪≫
      (DerivedCategory.homologyFunctor 𝒜 n).mapIso isoComplex
  let comparison (U : ιᵒᵖ) :
      homology.obj ((data.functor.obj U).obj K) ⟶
        (S.obj U).obj ((DerivedCategory.homologyFunctor 𝒜 n).obj K) :=
    homology.map ((data.functor.obj U).map isoComplex.inv) ≫
      homology.map (inv ((data.unit U.unop).app complex)) ≫
      factorsB.hom.app ((CanonicalMapOfComplexes.General.complexFunctor S U.unop).obj complex) ≫
      ((complex.sc n).mapHomologyIso (S.obj U)).hom ≫
      (S.obj U).map tailIso.hom
  let comparisonIso (U : ιᵒᵖ) :
      homology.obj ((data.functor.obj U).obj K) ≅
        (S.obj U).obj ((DerivedCategory.homologyFunctor 𝒜 n).obj K) :=
    homology.mapIso ((data.functor.obj U).mapIso isoComplex).symm ≪≫
      homology.mapIso (asIso ((data.unit U.unop).app complex)).symm ≪≫
      factorsB.app ((CanonicalMapOfComplexes.General.complexFunctor S U.unop).obj complex) ≪≫
      (complex.sc n).mapHomologyIso (S.obj U) ≪≫
      (S.obj U).mapIso tailIso
  have hcomparisonIso (U : ιᵒᵖ) : (comparisonIso U).hom = comparison U := rfl
  have hnatural {U V : ιᵒᵖ} (restriction : U ⟶ V) :
      homology.map ((data.functor.map restriction).app K) ≫ comparison V =
        comparison U ≫
          (S.map restriction).app ((DerivedCategory.homologyFunctor 𝒜 n).obj K) := by
    have hunit : (data.functor.map restriction).app (DerivedCategory.Q.obj complex) ≫
        inv ((data.unit V.unop).app complex) =
      inv ((data.unit U.unop).app complex) ≫
        DerivedCategory.Q.map
          ((CanonicalMapOfComplexes.General.restrictionComplex S restriction.unop).app
            complex) := by
      apply (cancel_mono ((data.unit V.unop).app complex)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [data.unit_restriction]
      simp
    have hfactor := factorsB.hom.naturality
      ((CanonicalMapOfComplexes.General.restrictionComplex S restriction.unop).app complex)
    have hbase :
        (HomologicalComplex.homologyFunctor ℬ (ComplexShape.up ℤ) n).map
            ((CanonicalMapOfComplexes.General.restrictionComplex S restriction.unop).app
              complex) ≫
            ((complex.sc n).mapHomologyIso (S.obj V)).hom =
          ((complex.sc n).mapHomologyIso (S.obj U)).hom ≫
            (S.map restriction).app (complex.sc n).homology :=
      mapHomologyIso_naturality_of_isZero_X₁ (complex.sc n) hzero (S.map restriction)
    have hhomology {X : ℬ} (x : (S.obj V).obj (complex.sc n).homology ⟶ X) :
        (HomologicalComplex.homologyFunctor ℬ (ComplexShape.up ℤ) n).map
            ((CanonicalMapOfComplexes.General.restrictionComplex S restriction.unop).app
              complex) ≫
            ((complex.sc n).mapHomologyIso (S.obj V)).hom ≫ x =
          ((complex.sc n).mapHomologyIso (S.obj U)).hom ≫
            (S.map restriction).app (complex.sc n).homology ≫ x :=
      (Category.assoc _ _ x).symm.trans
        ((congrArg (fun y ↦ y ≫ x) hbase).trans (Category.assoc _ _ x))
    have hrestriction := (S.map restriction).naturality tailIso.hom
    have hderived := congrArg homology.map
      ((data.functor.map restriction).naturality isoComplex.inv).symm
    have hunitHomology := congrArg homology.map hunit
    simp only [Functor.map_comp] at hderived hunitHomology
    dsimp only [comparison]
    simp only [Category.assoc] at *
    rw [reassoc_of% hderived, reassoc_of% hunitHomology, reassoc_of% hfactor, hhomology,
      hrestriction]
  let presheaf := data.functor ⋙ (evaluation _ _).obj K
  let sectionIso : presheaf ⋙ homology ≅
      S.flip.obj ((DerivedCategory.homologyFunctor 𝒜 n).obj K) :=
    NatIso.ofComponents comparisonIso (fun restriction ↦ by
      simp only [hcomparisonIso]
      exact hnatural restriction)
  have : D.IsCSquareIso K := hsquare
  have htriangle := D.cSquareTriangle_distinguished K
  obtain ⟨-, hbottom⟩ := exists_bottomDegreeIso_of_rightDerived
    (S.obj (op sq.X₁)) (data.functor.obj (op sq.X₁)) (data.unit sq.X₁)
    (fun I _ ↦ data.isIso_unit_app sq.X₁ I)
    K n hvanish
  have hpullback := isPullback_map_homologyFunctor_of_distTriang (sq.op.map presheaf).flip
    ((D.cSquareTriangle K).mor₃)
    (by convert htriangle using 1; rfl)
    n (hbottom (n - 1) (by omega))
  exact hpullback.flip.of_iso ((Square.mapFunctor.flip.obj sq.op).mapIso sectionIso)

end GeneralSystem

/-! ### Descent along the comparison of two topologies -/

section TwoTopologies

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}} {J' : GrothendieckTopology S.C}
  (h : J' ≤ S.J)
  [HasSheafify S.J AddCommGrpCat.{v}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

omit [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}] in
/-- **A `J'`-sheaf of modules whose underlying presheaf is a `J`-sheaf and whose inverse image
vanishes is zero.** Being a `J`-sheaf puts it in the essential image of `ε_*`, which is fully
faithful, so the unit of `ε^{-1} ⊣ ε_*` is invertible on it and identifies it with the image of
its vanishing inverse image. -/
private theorem isZero_of_isSheaf_of_modulePullback_isZero
    (M : SheafOfModules.{v} (ringSheafOfLe h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
    (hsheaf : Presheaf.IsSheaf S.J
      ((SheafOfModules.toSheaf (ringSheafOfLe h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O))).obj M).obj)
    (hzero : IsZero ((modulePullback.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).obj M)) : IsZero M := by
  have hfull := (fullyFaithfulModulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).full
  have hfaithful := (fullyFaithfulModulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).faithful
  have himage : (modulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).essImage M :=
    ⟨⟨M.val, hsheaf⟩, ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso (Iso.refl _)⟩⟩
  have : IsIso ((modulePullbackAdjPushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).unit.app M) :=
    ((modulePullbackAdjPushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).isIso_unit_app_iff_mem_essImage).2
      himage
  exact (((modulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O))).map_isZero hzero).of_iso
    (asIso ((modulePullbackAdjPushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).unit.app M))

/-- **The vanishing criterion.** Let `A` be a set and for each `α ∈ A` let a commutative square
`E α ⟶ Y α`, `Z α ⟶ X α` in `C` be given, and suppose that the family detects `J`-sheaves among
`J'`-sheaves of sets. Then an object of `D⁺(𝒪_{J'})` whose comparison maps for all these squares
are isomorphisms and whose inverse image `ε^{-1} K'` vanishes is itself zero.

The argument is an induction on the degree. If the cohomology of `K'` vanishes below `n`, then
`isPullback_sections_homology` makes the sections of `Hⁿ(K')` over each square a pullback square,
so the detection hypothesis makes `Hⁿ(K')` a `J`-sheaf; and `ε^{-1} Hⁿ(K') = Hⁿ(ε^{-1} K') = 0`
because `ε^{-1}` is exact, so `Hⁿ(K') = 0` by
`isZero_of_isSheaf_of_modulePullback_isZero`. -/
theorem isZero_of_forall_isCSquareIso_of_modulePullback_isZero
    {A : Type*} (sq : A → Square S.C)
    (hdetect : ∀ F : Sheaf J' (Type max u w),
      (∀ a, ((sq a).op.map F.obj).IsPullback) → Presheaf.IsSheaf S.J F.obj)
    (K' : DerivedCategory (SheafOfModules.{v} (ringSheafOfLe h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hplus : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{v} (ringSheafOfLe h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))).plus K')
    (hsquares : ∀ a, (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) (sq a)).IsCSquareIso K')
    (hzero : letI := modulePullback_additive.{u, v, w, r} h
                (Stacks.SheafOfModules.Tensor.ringSheaf S.O);
      letI := modulePullback_preservesFiniteLimits.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O);
      letI := modulePullback_preservesFiniteColimits.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O);
      IsZero ((modulePullback.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj K')) :
    IsZero K' := by
  have := modulePullback_additive.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := modulePullback_preservesFiniteLimits.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := modulePullback_preservesFiniteColimits.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} (ringSheafOfLe h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O))) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE (ringSheafOfLe h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
  let coarse := SheafOfModules.{v} (ringSheafOfLe h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
  have hbottom (n : ℤ)
      (hlower : ∀ i < n, IsZero ((DerivedCategory.homologyFunctor coarse i).obj K')) :
      IsZero ((DerivedCategory.homologyFunctor coarse n).obj K') := by
    let M := (DerivedCategory.homologyFunctor coarse n).obj K'
    let presheaf := ((SheafOfModules.toSheaf (ringSheafOfLe h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O))).obj M).obj
    have hpullback (a : A) :
        ((sq a).op.map (presheaf ⋙ forget AddCommGrpCat.{v})).IsPullback :=
      (isPullback_sections_homology.{u, v, w, r} (S := S.ofLe h) (sq a) K' n hlower
        (hsquares a)).map (forget AddCommGrpCat.{v})
    have hcoarse : Presieve.IsSheaf J' (presheaf ⋙ forget AddCommGrpCat.{v}) :=
      (isSheaf_iff_isSheaf_of_type _ _).1
        (Presheaf.isSheaf_comp_of_isSheaf J' presheaf (forget AddCommGrpCat.{v})
          ((SheafOfModules.toSheaf _).obj M).property)
    have hfine : Presieve.IsSheaf S.J (presheaf ⋙ forget AddCommGrpCat.{v}) :=
      isSheaf_of_forall_isPullback S.J (Set.range sq)
        (fun F hF ↦ hdetect F (fun a ↦ hF _ ⟨a, rfl⟩)) _ hcoarse
        (by rintro diagram ⟨a, rfl⟩; exact hpullback a)
    have hsheaf : Presheaf.IsSheaf S.J presheaf :=
      Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{v})
        ((isSheaf_iff_isSheaf_of_type _ _).2 hfine)
    have hpull : IsZero ((modulePullback.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).obj M) :=
      ((DerivedCategory.homologyFunctor (SheafOfModules.{v}
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) n).map_isZero
        hzero).of_iso (((modulePullback.{u, v, w, r} h
            (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategoryHomologyIso
            n).app K').symm
    exact isZero_of_isSheaf_of_modulePullback_isZero h M hsheaf hpull
  obtain ⟨bound, hbound⟩ := hplus
  have hvanish : ∀ i < bound, IsZero ((DerivedCategory.homologyFunctor coarse i).obj K') :=
    (DerivedCategory.isGE_iff K' bound).1 hbound
  have hall (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor coarse i).obj K') := by
    by_cases hi : i < bound
    · exact hvanish i hi
    · have hstep : ∀ offset : ℕ,
          IsZero ((DerivedCategory.homologyFunctor coarse (bound + offset)).obj K') := by
        intro offset
        induction offset using Nat.strong_induction_on with
        | h offset hypothesis =>
          apply hbottom
          intro j hj
          by_cases hsmall : j < bound
          · exact hvanish j hsmall
          · have heq : j = bound + (j - bound).toNat := by omega
            rw [heq]
            exact hypothesis (j - bound).toNat (by omega)
      have heq : i = bound + (i - bound).toNat := by omega
      rw [heq]
      exact hstep _
  have : IsIso (0 : K' ⟶ K') := (DerivedCategory.isIso_iff coarse (0 : K' ⟶ K')).2 (by
    intro i
    have heq : (DerivedCategory.homologyFunctor coarse i).map (0 : K' ⟶ K') =
        𝟙 ((DerivedCategory.homologyFunctor coarse i).obj K') := (hall i).eq_of_src _ _
    rw [heq]
    infer_instance)
  exact (IsZero.iff_id_eq_zero K').2
    (by simpa only [zero_comp] using (IsIso.hom_inv_id (0 : K' ⟶ K')).symm)

end TwoTopologies

/-! ### Stacks 0F18 -/

section Main

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}} {J' : GrothendieckTopology S.C}
  (h : J' ≤ S.J)
  [HasSheafify S.J AddCommGrpCat.{v}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- **Stacks 0F18.** Let `C` carry two Grothendieck topologies `J' ≤ J` and let `𝒪` be a sheaf of
rings for `J`, so that the identity of `C` is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. Let `A` be a type and for each `α : A` let

```
E α ⟶ Y α
  ↓      ↓
Z α ⟶ X α
```

be a commutative square in `C`. Assume

1. a `J'`-sheaf of sets `F'` is a `J`-sheaf whenever
   `F'(X α) = F'(Z α) ×_{F'(E α)} F'(Y α)` for all `α`, and
2. for every `K'` in `D(𝒪_{J'})` in the essential image of `Rε_*` the canonical comparison maps
   `c^{K'}_{X α, Z α, Y α, E α}` of [Stacks, Tag 0F16] are isomorphisms for all `α`.

Then an object `K'` of `D⁺(𝒪_{J'})` lies in the essential image of `Rε_*` if and only if the
maps `c^{K'}_{X α, Z α, Y α, E α}` are isomorphisms for all `α`.

`Rε_*` is any right derived functor of `ε_*` together with its unit; the hypothesis that it is a
right derived functor is what makes the essential image independent of the choice. -/
@[stacks 0F18]
theorem essImage_iff_forall_isCSquareIso {A : Type*} (sq : A → Square S.C)
    (hdetect : ∀ F : Sheaf J' (Type max u w),
      (∀ a, ((sq a).op.map F.obj).IsPullback) → Presheaf.IsSheaf S.J F.obj)
    (Rε : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ⥤
      DerivedCategory (SheafOfModules.{v} (ringSheafOfLe h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (η : letI := modulePushforward_additive.{u, v, w, r} h
            (Stacks.SheafOfModules.Tensor.ringSheaf S.O);
      (modulePushforward.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{v}
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) (ComplexShape.up ℤ))]
    (hcomparison : ∀ K' : DerivedCategory (SheafOfModules.{v} (ringSheafOfLe h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O))),
      Rε.essImage K' → ∀ a, (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) (sq a)).IsCSquareIso K')
    (K' : DerivedCategory (SheafOfModules.{v} (ringSheafOfLe h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hplus : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{v} (ringSheafOfLe h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))).plus K') :
    Rε.essImage K' ↔ ∀ a, (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) (sq a)).IsCSquareIso K' := by
  have := modulePushforward_additive.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := modulePullback_additive.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := modulePullback_preservesFiniteLimits.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := modulePullback_preservesFiniteColimits.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  refine ⟨hcomparison K', fun hsquares ↦ ?_⟩
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have := (fullyFaithfulModulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).full
  have := (fullyFaithfulModulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).faithful
  have : PreservesFiniteLimits (modulePushforward.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) :=
    ⟨fun _ ↦ (modulePullbackAdjPushforward.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf
      S.O)).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩
  let derivedAdj := mapDerivedCategoryAdjunction
    (modulePullback.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
    (modulePushforward.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
    (modulePullbackAdjPushforward.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) Rε η
  let fullyFaithful := fullyFaithfulOfDerivedAdjunction
    (modulePullback.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
    (modulePushforward.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
    (modulePullbackAdjPushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) Rε η derivedAdj
  have := fullyFaithful.full
  have := fullyFaithful.faithful
  obtain ⟨bound, hbound⟩ := hplus
  have hleft : ((modulePullback.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj K').IsGE
      bound :=
    (DerivedCategory.isGE_iff _ _).2 (fun i hi ↦
      ((modulePullback.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).map_isZero
        ((DerivedCategory.isGE_iff K' _).1 hbound i hi)).of_iso
        (((modulePullback.{u, v, w, r} h
            (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategoryHomologyIso i).app K'))
  have hright : (Rε.obj ((modulePullback.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj
      K')).IsGE bound :=
    isGE_rightDerived_obj (modulePushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) Rε η _ _ hleft
  obtain ⟨cone, hconeplus, second, third, htriangle⟩ :=
    (DerivedCategory.TStructure.t
      (C := SheafOfModules.{v} (ringSheafOfLe h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))).plus.distinguished_cocone_triangle
      (derivedAdj.unit.app K') ⟨bound, hbound⟩ ⟨bound, hright⟩
  have hconeSquares (a : A) : (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) (sq a)).IsCSquareIso cone :=
    CanonicalMapOfComplexes.isCSquareIso_obj₃_of_distTriang.{u, v} (S := S.ofLe h) (sq a)
      (Triangle.mk (derivedAdj.unit.app K') second third) htriangle (hsquares a)
      (hcomparison _ ⟨(modulePullback.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj K',
        ⟨Iso.refl _⟩⟩ a)
  have hmapUnit : IsIso ((modulePullback.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.map
      (derivedAdj.unit.app K')) := by
    have hequal : (modulePullback.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.map
          (derivedAdj.unit.app K') =
        inv (derivedAdj.counit.app
          ((modulePullback.{u, v, w, r} h
              (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj K')) := by
      apply (cancel_mono (derivedAdj.counit.app
        ((modulePullback.{u, v, w, r} h
            (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj K'))).1
      simpa only [IsIso.inv_hom_id, Functor.id_obj] using
        derivedAdj.left_triangle_components K'
    rw [hequal]
    infer_instance
  have hconeZero : IsZero ((modulePullback.{u, v, w, r} h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.obj
      cone) :=
    ((modulePullback.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.mapTriangle.obj
      (Triangle.mk (derivedAdj.unit.app K') second third)).isZero₃_of_isIso₁
      ((modulePullback.{u, v, w, r} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapDerivedCategory.map_distinguished _
        htriangle) hmapUnit
  have : IsIso (derivedAdj.unit.app K') :=
    ((Triangle.mk (derivedAdj.unit.app K') second third).isZero₃_iff_isIso₁ htriangle).1
      (isZero_of_forall_isCSquareIso_of_modulePullback_isZero h sq hdetect cone hconeplus
        hconeSquares hconeZero)
  exact derivedAdj.mem_essImage_of_unit_isIso K'

end Main

end Stacks.Cohomology.MayerVietoris

end

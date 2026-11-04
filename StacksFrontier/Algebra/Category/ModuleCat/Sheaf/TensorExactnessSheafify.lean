module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksCore.Tactic.StacksAttribute

/-!
# Kernels of surjections onto finitely presented sheaves of modules

Let `R` be a sheaf of rings on a site `(C, J)`. Stacks Tag 01BP says that if `F` is a sheaf of
`R`-modules of finite presentation and `θ : G ⟶ F` is a surjection with `G` of finite type, then
`Ker θ` is of finite type; in particular this applies when `G` is a finite free sheaf of modules.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel` proves the whole mathematical
content of the tag for a target with a **global** finite presentation and a source generated
by finitely many **global** sections. This file closes the remaining gap, which is one of
locality rather than of mathematics: `SheafOfModules.IsFinitePresentation` and
`SheafOfModules.IsFiniteType` only provide a presentation and a family of generators after
passing to a covering family, and the two covering families need not agree.

The reduction runs as follows. Restriction of a presentation, respectively of a family of
generating sections, along an arbitrary morphism `f : W ⟶ V` of the site is available as soon as
`SheafOfModules.overMap R f` preserves colimits, so that it preserves the cokernel
presentations; this is `presentationOver` and `generatingSectionsOver`. Intersecting
the covering sieve on which `F` has a finite presentation with the one on which `G` has finite
generators therefore produces a covering sieve all of whose members carry **both** pieces of
data globally, and over such a member the globally presented theorem
`FiniteTypeKernel.isFiniteType_kernel_of_presentation` applies on the slice site. Finally the
conclusion, being of finite type, is local on the base: that is `isFiniteType_of_coversTop`,
whose construction `bindLocalGeneratorsData` is the family-of-generators analogue of
`SheafOfModules.QuasicoherentData.bind`.

## Main definitions

* `Stacks.SheafOfModules.LocalKernel.presentationOver` and
  `Stacks.SheafOfModules.LocalKernel.generatingSectionsOver`: restriction of a presentation,
  respectively of a family of generating sections, of `M.over V` along a morphism `W ⟶ V` of the
  site.
* `Stacks.SheafOfModules.LocalKernel.generatingSectionsIteratedSlice`: generating sections of a
  twice restricted sheaf of modules `(M.over W).over Z`, read as generating sections of
  `M.over Z.left` along `Over.iteratedSliceEquiv`.
* `Stacks.SheafOfModules.LocalKernel.bindLocalGeneratorsData`: local generators of the
  restrictions of `M` to the members of a covering family, glued into local generators of `M`.

## Main results

* `Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop`: being of finite type is local
  on the base. Mathlib has this for quasicoherence (`SheafOfModules.IsQuasicoherent.of_coversTop`)
  but not for finite type, because it has no `bind` for families of generating sections.
* `Stacks.SheafOfModules.LocalKernel.isFiniteType_kernel_over`: over an object of the site
  carrying both a finite presentation of the target and finitely many generators of the source,
  the kernel of a surjection is of finite type.
* `Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType` and
  `Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finite_free`: **Stacks Tag
  01BP**, parts (2) and (1), in the local senses of finite presentation and finite type.

## Implementation notes

Nothing is specialised: the site `C : Type u₁` has `Category.{v₁} C` and the sheaf of rings is
`R : Sheaf J RingCat.{u}` with `u`, `u₁`, `v₁` unrelated, which is the generality in which
Mathlib states `SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`.

The instance hypotheses are exactly those under which the argument takes place, and they are all
satisfied on the site of opens of a topological space, which is the ringed-space case Stacks
01BP is stated for. Three groups deserve comment.

* `HasSheafify` rather than `HasWeakSheafify`, on `J` and on each slice topology `J.over X`:
  `Abelian (SheafOfModules.{u} R)` is transferred along the sheafification adjunction and so
  needs sheafification to be left exact. `HasWeakSheafify` suffices to *state* `IsFiniteType`,
  which is why it is tempting, but the proof forms kernels, cokernels and biproducts of sheaves
  of modules both on `J` and on its slices.
* The twice iterated slices `((J.over X).over Z)` carry the same two hypotheses. This is forced
  by the gluing step and is the same hypothesis set Mathlib's
  `SheafOfModules.QuasicoherentData.bind` carries: a local datum for `M.over X` lives over an
  object `Z` of `Over X`, and turning it into a datum for `M.over Z.left` is the transport along
  `Over.iteratedSliceEquiv`.
* Colimit preservation by the restriction functors, in the three forms the argument uses:
  restriction to a slice site of the base, restriction to a slice site of a slice site, and
  restriction along a morphism of the base. These are *assumed*, not derived. Mathlib derives
  them from `HasBinaryProducts C` and `HasPullbacks C`, which make the restrictions left
  adjoints (`SheafOfModules.overPushforwardOverAdj`, `SheafOfModules.overMapPushforwardAdj`),
  and a site with those products satisfies the hypotheses by instance search. But a site need
  have no finite limits at all — Stacks Tag 082T is this statement for an arbitrary ringed site
  — and the restrictions still preserve colimits, because `Over.forget V` and `Over.map f` are
  continuous and cocontinuous. Assuming the colimit preservation rather than the products is
  what lets both cases use this file.

`hasBinaryProducts_over` is deliberately *not* a global instance: Mathlib keeps
`CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback` a theorem, and promoting
it would add a global instance whose search can chain through further slice categories. It is no
longer needed here and is kept only as that restatement.

Despite the file name, nothing about tensor products or about Tag 03EX occurs in this file; only
Tag 01BP is proved here.

## References

* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

universe u v₁ u₁

namespace Stacks.SheafOfModules.LocalKernel

section Restrict

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u} (overMap.{u} R f)]

/-- Restriction of a presentation of `M.over V` along a morphism `f : W ⟶ V` of the site, as a
presentation of `M.over W`. -/
noncomputable def presentationOver {M : SheafOfModules.{u} R} {V W : C} (f : W ⟶ V)
    (P : (M.over V).Presentation) : (M.over W).Presentation :=
  (P.map (overMap R f) (overMapUnitIso f).symm).ofIsIso ((overFunctorMap R f).app M).hom

/-- The restriction `presentationOver f P` of a finite presentation `P` along `f` is finite. -/
instance presentationOver_isFinite {M : SheafOfModules.{u} R} {V W : C} (f : W ⟶ V)
    (P : (M.over V).Presentation) [P.IsFinite] : (presentationOver f P).IsFinite := by
  have h₁ : ((P.map (overMap R f) (overMapUnitIso f).symm)).IsFinite := by
    constructor
    · exact ⟨by simpa using (inferInstance : Finite P.generators.I)⟩
    · exact ⟨by simpa using (inferInstance : Finite P.relations.I)⟩
  exact inferInstanceAs (Presentation.IsFinite (Presentation.ofIsIso _ _))

/-- Restriction of a family of generating sections of `M.over V` along a morphism `f : W ⟶ V` of
the site, as a family of generating sections of `M.over W`. -/
noncomputable def generatingSectionsOver {M : SheafOfModules.{u} R} {V W : C} (f : W ⟶ V)
    (gs : (M.over V).GeneratingSections) : (M.over W).GeneratingSections :=
  (gs.map (overMap R f) (overMapUnitIso f).symm).ofEpi ((overFunctorMap R f).app M).hom

/-- The restriction `generatingSectionsOver f gs` along `f` of a finite family of generating
sections `gs` is finite. -/
instance generatingSectionsOver_isFiniteType {M : SheafOfModules.{u} R} {V W : C} (f : W ⟶ V)
    (gs : (M.over V).GeneratingSections) [gs.IsFiniteType] :
    (generatingSectionsOver f gs).IsFiniteType :=
  inferInstanceAs (GeneratingSections.IsFiniteType (GeneratingSections.ofEpi _ _))

end Restrict

section Bind

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Generating sections of the twice restricted sheaf of modules `(M.over W).over Z`, read as
generating sections of `M.over Z.left` along `Over.iteratedSliceEquiv`. -/
noncomputable def generatingSectionsIteratedSlice {M : SheafOfModules.{u} R} {W : C}
    (Z : Over W) (s : ((M.over W).over Z).GeneratingSections) :
    (M.over Z.left).GeneratingSections :=
  letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Z)
    (S := (R.over W).over Z) (R := R.over Z.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  (s.map e.inverse (.refl _)).ofEpi
    (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over W).over Z))).hom

/-- The family of generating sections `generatingSectionsIteratedSlice Z s` is finite when `s` is
finite. -/
instance generatingSectionsIteratedSlice_isFiniteType {M : SheafOfModules.{u} R} {W : C}
    (Z : Over W) (s : ((M.over W).over Z).GeneratingSections) [s.IsFiniteType] :
    (generatingSectionsIteratedSlice Z s).IsFiniteType :=
  ⟨inferInstanceAs (Finite s.I)⟩

/-- Local generators of the restrictions of `M` to the members of a covering family, glued into
local generators of `M` itself: the datum indexed by `⟨i, j⟩` is the one of `D i` at `j`,
transported from the iterated slice `(M.over (Xc i)).over ((D i).X j)` down to the base object
`((D i).X j).left`. This is the family-of-generators analogue of
`SheafOfModules.QuasicoherentData.bind`, and is built the same way. -/
noncomputable def bindLocalGeneratorsData (M : SheafOfModules.{u} R) {I : Type u₁}
    (Xc : I → C) (hX : J.CoversTop Xc)
    (D : Π i, (M.over (Xc i)).LocalGeneratorsData.{max u₁ v₁}) :
    M.LocalGeneratorsData.{max u₁ v₁} where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  generators ij := generatingSectionsIteratedSlice _ ((D ij.1).generators ij.2)

/-- The glued local generators `bindLocalGeneratorsData M Xc hX D` are of finite type when each
`D i` is of finite type. -/
instance bindLocalGeneratorsData_isFiniteType (M : SheafOfModules.{u} R) {I : Type u₁}
    (Xc : I → C) (hX : J.CoversTop Xc)
    (D : Π i, (M.over (Xc i)).LocalGeneratorsData.{max u₁ v₁})
    [hD : ∀ i, (D i).IsFiniteType] :
    (bindLocalGeneratorsData M Xc hX D).IsFiniteType where
  isFiniteType ij :=
    have := (hD ij.1).isFiniteType ij.2
    ⟨inferInstanceAs (Finite ((D ij.1).generators ij.2).I)⟩

/-- If the local generators `q` are of finite type, then so is their shrinking `q.shrink`. -/
instance shrink_isFiniteType {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData.{max u₁ v₁}) [hq : q.IsFiniteType] :
    (q.shrink).IsFiniteType where
  isFiniteType _ := hq.isFiniteType _

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Being of finite type is local on the base.** If the members of a covering family of the
terminal object all have finite type restrictions of `M`, then `M` is of finite type. -/
theorem isFiniteType_of_coversTop (M : SheafOfModules.{u} R) {I : Type u₁}
    (Xc : I → C) (hX : J.CoversTop Xc) (h : ∀ i, (M.over (Xc i)).IsFiniteType) :
    M.IsFiniteType := by
  choose D hD using fun i ↦ (h i).exists_localGeneratorsData
  exact ⟨⟨(bindLocalGeneratorsData M Xc hX D).shrink,
    have : ∀ i, (D i).IsFiniteType := hD
    inferInstance⟩⟩

end Bind

section Main

section Pullbacks

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]

end Pullbacks

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : C, PreservesColimitsOfSize.{u, u} (overFunctor.{u} R V)]
  [∀ (V : C) (Z : Over V), PreservesColimitsOfSize.{u, u} (overFunctor.{u} (R.over V) Z)]
  [∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u} (overMap.{u} R f)]

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (V : C) (Z : Over V), PreservesColimitsOfSize.{u, u} (overFunctor.{u} (R.over V) Z)]
  [∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u} (overMap.{u} R f)] in
/-- The restriction `p.over V` of an epimorphism `p` of sheaves of modules to an object `V` of the
site is an epimorphism: `SheafOfModules.overFunctor` preserves colimits and therefore
epimorphisms. -/
theorem over_epi {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Epi p] (V : C) :
    Epi (p.over V) := by
  have : PreservesColimitsOfSize.{0, 0} (overFunctor.{u} R V) :=
    preservesColimitsOfSize_shrink _
  have h : (overFunctor.{u} R V).PreservesEpimorphisms := by
    have : PreservesColimitsOfShape WalkingSpan (overFunctor.{u} R V) := inferInstance
    infer_instance
  exact h.preserves p

/-- The free sheaf of modules `free I` on a finite type `I` is of finite type: the trivial
covering of the site witnesses it. -/
-- Not a duplicate of `Stacks.SheafOfModules.isFiniteType_free` in `Coherent`: that one needs
-- `HasWeakSheafify`, `WEqualsLocallyBijective` and a per-slice `HasSheafify`, and this proof needs
-- none of them, so routing consumers at it would add hypotheses.
instance isFiniteType_free (I : Type u) [Finite I] :
    (free I : SheafOfModules.{u} R).IsFiniteType :=
  ⟨⟨FiniteTypeKernel.localGeneratorsDataOfGeneratingSections
      (free.generatingSections (R := R) I),
    ⟨fun _ ↦ ⟨inferInstanceAs (Finite I)⟩⟩⟩⟩

omit [∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u} (overMap.{u} R f)] in
/-- Over an object `V` of the site where the target has a finite presentation and the source has
finitely many generating sections, the restriction to `V` of the kernel of a surjection is of
finite type. This is `FiniteTypeKernel.isFiniteType_kernel_of_presentation` run on the slice
site over `V`, together with the identification of `(kernel θ).over V` with
`kernel (θ.over V)`. -/
theorem isFiniteType_kernel_over {F G : SheafOfModules.{u} R} (θ : G ⟶ F) [Epi θ] (V : C)
    (P : (F.over V).Presentation) [P.IsFinite]
    (gs : (G.over V).GeneratingSections) [gs.IsFiniteType] :
    ((kernel θ).over V).IsFiniteType := by
  have : Epi (θ.over V) := over_epi θ V
  have := FiniteTypeKernel.isFiniteType_kernel_of_presentation P gs (θ.over V)
  exact Stacks.SheafOfModules.isFiniteType_of_epi
    (PreservesKernel.iso (overFunctor R V) θ).inv this

/-- The kernel of a surjection from a finite-type sheaf of modules onto a finitely presented sheaf
of modules is of finite type. -/
@[stacks 01BP "part (2)"]
instance kernel_isFiniteType_of_epi_from_finiteType {F G : SheafOfModules.{u} R}
    [F.IsFinitePresentation] [G.IsFiniteType] (theta : G ⟶ F) [Epi theta] :
    (kernel theta).IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData G
  refine isFiniteType_of_coversTop _
    (Subtype.val : { V : C // ((kernel theta).over V).IsFiniteType } → C) ?_ fun i ↦ i.2
  intro Y
  refine J.superset_covering ?_
    (J.intersection_covering (q.coversTop Y) (σ.coversTop Y))
  rintro V g ⟨hg₁, hg₂⟩
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg₁
  obtain ⟨j, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg₂
  have := hq.isFinite_presentation i
  have := hσ.isFiniteType j
  exact (Sieve.mem_ofObjects_iff _ g).2
    ⟨⟨V, isFiniteType_kernel_over theta V (presentationOver a (q.presentation i))
      (generatingSectionsOver b (σ.generators j))⟩, ⟨𝟙 V⟩⟩

/-- The kernel of a surjection from a finite-rank free sheaf of modules onto a finitely
presented sheaf of modules is of finite type, as an instance, from part (2) above.

Part (1) of Tag 01BP is registered on
`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi_from_finite_free`, which states
the same thing under four instance hypotheses rather than the ten this one inherits from part
(2), with no products and no pullbacks on the site. This declaration stays because it is the
`instance` that instance search reaches from the modules downstream of this file. -/
instance kernel_isFiniteType_of_epi_from_finite_free {I : Type u} [Finite I]
    {F : SheafOfModules.{u} R} [F.IsFinitePresentation] (psi : free I ⟶ F) [Epi psi] :
    (kernel psi).IsFiniteType :=
  kernel_isFiniteType_of_epi_from_finiteType psi

end Main

end Stacks.SheafOfModules.LocalKernel

end

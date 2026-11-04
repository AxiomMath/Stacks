module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.FirstVariable
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The local kernel description of an internal Hom

Let `(X, 𝒪_X)` be a ringed space and let `F`, `G` be `𝒪_X`-modules with `F` of finite
presentation. [Stacks, Tag 01CQ] asserts, in its first clause, that `SheafHom(F, G)` is
*locally a kernel of a map between finite direct sums of copies of `G`*, and deduces in its
second clause that `SheafHom(F, G)` is coherent whenever `G` is. This file proves the first
clause; the second follows from it and
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`, which is the gluing step
already available in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean`, so both clauses of 01CQ
end up proved here.

The argument is the one of the source, which is the argument in the proof of
[Stacks, Tag 01CP]. Shrinking to an open `U` on which `F` admits a finite presentation
`𝒪_U^{⊕ n} → 𝒪_U^{⊕ m} → F|_U → 0`, left exactness of internal Hom in its first variable
([Stacks, Tag 03EN], which is `internalHomFirstFunctor_preservesColimitsOfSize`) turns that
cokernel into a kernel

`0 → SheafHom(F|_U, G|_U) → SheafHom(𝒪_U^{⊕ m}, G|_U) → SheafHom(𝒪_U^{⊕ n}, G|_U)`,

and internal Hom out of a finite free module is the corresponding finite direct sum, because
internal Hom carries the coproduct `𝒪_U^{⊕ m} = ∐_{i < m} 𝒪_U` to a product and `SheafHom(𝒪, G)`
is `G`. Finally `SheafHom(F, G)|_U` is `SheafHom(F|_U, G|_U)` by [Stacks, Tag 0E8H].

## Main definitions

* `Stacks.SheafOfModules.InternalHom.spaceRingedSite`: a ringed space read as a ringed site, so
  that the internal Hom API of a ringed site applies to it.
* `Stacks.SheafOfModules.InternalHom.unitInternalHomIso` and `unitSheafInternalHomIso`:
  `SheafHom(𝒪, G) ≅ G`.
* `Stacks.SheafOfModules.InternalHom.freeSheafInternalHomIso`:
  `SheafHom(𝒪^{⊕ I}, G) ≅ ∐_{i ∈ I} G` for a finite index type `I`.
* `Stacks.SheafOfModules.InternalHom.presentationSheafInternalHomIso`: a global presentation of `F`
  exhibits `SheafHom(F, G)` as a kernel.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomOverIso`: [Stacks, Tag 0E8H] in the form
  `SheafHom(F, G)|_U ≅ SheafHom(F|_U, G|_U)`.

## Main results

* `Stacks.SheafOfModules.InternalHom.exists_isoKernel_sheafInternalHom`: if `F` admits a
  *global* finite presentation then `SheafHom(F, G)` is the kernel of a map
  `∐_{i < m} G ⟶ ∐_{j < n} G`.
* `Stacks.SheafOfModules.InternalHom.exists_locally_isoKernel_sheafInternalHom`:
  **the first clause of [Stacks, Tag 01CQ]**. On a ringed space, for `F` of finite presentation,
  every point has an open neighbourhood `U` on which `SheafHom(F, G)|_U` is the kernel of a map
  `∐_{i < m} G|_U ⟶ ∐_{j < n} G|_U`.
* `Stacks.SheafOfModules.InternalHom.isCoherent_sheafInternalHom` and
  `isCoherent_sheafInternalHom'`: **the second clause of [Stacks, Tag 01CQ]**, in the two
  spellings of coherence carried by this branch (see the implementation notes).
* `Stacks.SheafOfModules.InternalHom.isFinitePresentation_sheafInternalHom`: the internal Hom from
  a module of finite presentation into a coherent module is of finite presentation. This is the
  form in which [Stacks, Tag 01Y2] is consumed by the reflexivity theory.

## Implementation notes

**Which coherence predicate.** This branch carries two classes with the same two fields:
`SheafOfModules.IsCoherent` of Stacks Tag 01BW and
`Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`. They are interchangeable by
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff`. The gluing step of 01CQ is stated for
the second, and `isFinitePresentation_of_isCoherent` for the first, so both conclusions are
recorded: `isCoherent_sheafInternalHom'` for the first class — written
`_root_.SheafOfModules.IsCoherent` throughout, since inside the `Stacks` namespace the
unqualified name and dot notation both resolve to the second — and `isCoherent_sheafInternalHom`
for the second, which is the class carrying `@[stacks 01BV "the coherence predicate"]` and
therefore the one the 01CQ attribute is placed on.

**Why the whole argument runs on the localized ringed site.** The presentation of `F` supplied
by `SheafOfModules.IsFinitePresentation` is a presentation of `F.over U` on the slice site over
`U`, not a presentation of `F`. Rather than transporting it back, the global statement
`exists_isoKernel_sheafInternalHom` is proved for an arbitrary ringed site and then
applied to `AlgebraicGeometry.RingedSite.over X U`; the only thing that has to be said about the
original site is `sheafInternalHomOverIso`, which is [Stacks, Tag 0E8H].

**`SheafHom(𝒪, G) ≅ G` is not proved by hand.** It is the uniqueness of right adjoints: the
tensor–internal-Hom adjunction of [Stacks, Tag 03EO],
`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction`, makes internal Hom out of
`G` right adjoint to `- ⊗ G`, and for `G = 𝒪` the left adjoint is the right unitor, isomorphic to
the identity; so internal Hom out of `𝒪` is isomorphic to the identity functor. This happens at
the level of presheaves of modules and is carried to sheaves by the fully faithful forgetful
functor, the internal Hom of sheaves of modules being the internal-Hom presheaf on the nose.

**Universes.** Everything is equi-universe, `RingedSite.{u, u, u}` with `SheafOfModules.{u}`,
for the reason recorded in
`StacksFrontier/AlgebraicGeometry/InternalHomCoherent/FirstVariable.lean`: the internal Hom of
two `SheafOfModules.{w}` on a `RingedSite.{u, v, w}` lands in `SheafOfModules.{max u v w}`.

**The `@[stacks 01CQ]` attributes.** Both clauses of the tag are proved here, so the tag's
covering set is complete, and it is carried by the two declarations that state the two clauses:
`exists_locally_isoKernel_sheafInternalHom` and `isCoherent_sheafInternalHom`. Nothing else in
the library carried a 01CQ attribute before. In particular
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct` does not and should not: it is
the gluing step, which is Stacks 01BY (1) in local form, not 01CQ. The duplicate
`isCoherent_sheafInternalHom'` is untagged.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open TopologicalSpace
open Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

universe u

/-! ### Internal Hom out of the structure sheaf -/

section Presheaf

variable {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})

/-- **Internal Hom out of the structure sheaf is the identity functor.** By [Stacks, Tag 03EO]
internal Hom out of `G` is right adjoint to `- ⊗ G`; for `G = 𝒪` that left adjoint is the right
unitor, which is isomorphic to the identity, and right adjoints are unique. -/
def unitInternalHomFunctorIso :
    𝟭 (PresheafOfModules.{u} (Oforget O)) ≅
      internalHomSecondFunctor.{u, u, u, u} O (PresheafOfModules.unit (Oforget O)) :=
  Adjunction.rightAdjointUniq Adjunction.id
    ((presheafTensorHomAdjunction O (PresheafOfModules.unit (Oforget O))).ofNatIsoLeft
      (rightUnitorNatIso (PresheafOfModules.{u} (Oforget O))))

/-- `Hom_𝒪(𝒪, G) ≅ G` for presheaves of modules. -/
def unitInternalHomIso (G : PresheafOfModules.{u} (Oforget O)) :
    internalHom O (PresheafOfModules.unit (Oforget O)) G ≅ G :=
  ((unitInternalHomFunctorIso O).app G).symm

end Presheaf

/-! ### Internal Hom out of a finite free module -/

section FiniteFree

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `SheafHom(𝒪, G) ≅ G`: the presheaf statement `unitInternalHomIso`, carried to sheaves of
modules along the fully faithful forgetful functor. -/
def unitSheafInternalHomIso (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    sheafInternalHom X (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) G ≅
      G :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso (unitInternalHomIso X.O.obj G.val)

/-- **`SheafHom(𝒪^{⊕ I}, G) ≅ ∐_{i ∈ I} G` for a finite index type.** Internal Hom in the first
variable carries the coproduct `𝒪^{⊕ I} = ∐_{i ∈ I} 𝒪` to a product of copies of
`SheafHom(𝒪, G) = G`, and a finite product in an additive category is a finite coproduct. -/
def freeSheafInternalHomIso (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (I : Type u) [Finite I] :
    sheafInternalHom X (_root_.SheafOfModules.free I) G ≅
      ∐ (fun _ : I => G) :=
  let _ : HasBiproduct (fun _ : I => G) := HasBiproduct.of_hasProduct _
  (PreservesCoproduct.iso (internalHomFirstFunctor X G)
        (fun _ : I =>
          _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).unop.symm ≪≫
    (opProductIsoCoproduct (fun _ : I =>
      sheafInternalHom X
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) G)).unop ≪≫
    Pi.mapIso (fun _ => unitSheafInternalHomIso X G) ≪≫
    (biproduct.isoProduct (fun _ : I => G)).symm ≪≫
    biproduct.isoCoproduct (fun _ : I => G)

end FiniteFree

/-! ### The kernel description from a global presentation -/

section Presentation

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **A presentation of `F` exhibits `SheafHom(F, G)` as a kernel.** If
`free P.relations.I → free P.generators.I → F → 0` is the exact sequence attached to a
presentation `P` of `F`, then internal Hom against `G`, which carries colimits to limits by
[Stacks, Tag 03EN], carries that cokernel to the kernel of the induced map
`SheafHom(free P.generators.I, G) ⟶ SheafHom(free P.relations.I, G)`. -/
def presentationSheafInternalHomIso
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (P : F.Presentation) :
    sheafInternalHom X F G ≅
      kernel (internalHomMapLeft X G (P.relations.π ≫ kernel.ι P.generators.π)) :=
  have hab : (P.relations.π ≫ kernel.ι P.generators.π) ≫ P.generators.π = 0 := by simp
  have he : (ShortComplex.mk _ _ hab).Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have h : kernel.lift P.generators.π (P.relations.π ≫ kernel.ι P.generators.π) hab
        = P.relations.π := by
      apply (cancel_mono (kernel.ι P.generators.π)).1
      rw [kernel.lift_ι]
    rw [h]
    infer_instance
  (CokernelCofork.IsColimit.ofπUnop _ _
    (isColimitCoforkMapOfIsColimit' (internalHomFirstFunctor X G) hab
      he.gIsCokernel)).conePointUniqueUpToIso (limit.isLimit _)

/-- **`SheafHom(F, G)` is a kernel of a map between finite direct sums of copies of `G`**, for
`F` carrying a global finite presentation. This is the first clause of [Stacks, Tag 01CQ] in the
case where the presentation is global; the general case is obtained from it by restricting to an
open on which a finite presentation exists. -/
theorem exists_isoKernel_sheafInternalHom
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (P : F.Presentation)
    (hP : P.IsFinite) :
    ∃ (m n : ℕ) (f : (∐ fun _ : Fin m => G) ⟶ (∐ fun _ : Fin n => G)),
      Nonempty (sheafInternalHom X F G ≅ kernel f) := by
  classical
  have := hP
  let _ := Fintype.ofFinite P.generators.I
  let _ := Fintype.ofFinite P.relations.I
  let e := freeSheafInternalHomIso X G P.generators.I ≪≫
    Sigma.reindex (Fintype.equivFin P.generators.I) (fun _ => G)
  let d := freeSheafInternalHomIso X G P.relations.I ≪≫
    Sigma.reindex (Fintype.equivFin P.relations.I) (fun _ => G)
  refine ⟨_, _, e.inv ≫ internalHomMapLeft X G
    (P.relations.π ≫ kernel.ι P.generators.π) ≫ d.hom, ⟨?_⟩⟩
  exact presentationSheafInternalHomIso X G P ≪≫ kernel.mapIso _ _ e d (e.hom_inv_id_assoc _).symm

end Presentation

/-! ### Restriction to an open, and the local statement -/

section Local

/-- **[Stacks, Tag 0E8H] for `sheafHom`.** Restricting an internal Hom to the localized ringed
site over `U` gives the internal Hom of the restrictions. This is
`Stacks.SheafOfModules.InternalHom.internalHomOverIso` carried from presheaves of modules to
sheaves of modules; the two internal Homs have the same underlying presheaf of modules on the
nose, so the fully faithful forgetful functor suffices. -/
def sheafInternalHomOverIso (X : RingedSite.{u, u, u}) (U : X.C)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafInternalHom X F G).over U ≅
      sheafInternalHom (X.over U) (F.over U) (G.over U) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso (internalHomOverIso X U F G)

/-- A ringed space read as a ringed site: the site of its opens, with its structure sheaf. -/
abbrev spaceRingedSite {Y : Type u} [TopologicalSpace Y]
    (O : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) : RingedSite.{u, u, u} where
  C := Opens Y
  J := Opens.grothendieckTopology Y
  O := O

variable {Y : Type u} [TopologicalSpace Y]
  (O : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})

/-- A module of finite presentation admits, around every point, an open neighbourhood on which
it has a finite presentation. This is the content of `SheafOfModules.IsFinitePresentation`
read at a point: the quasi-coherent data it provides is a cover of the space by opens carrying
finite presentations. -/
theorem exists_isFinite_presentation_of_mem
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [F.IsFinitePresentation] (y : Y) :
    ∃ U : Opens Y, y ∈ U ∧ ∃ P : (F.over U).Presentation, P.IsFinite := by
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  have hy : y ∈ iSup q.X := by
    have hcover : iSup q.X = ⊤ := ((Opens.coversTop_iff Y q.X).mp q.coversTop).iSup_eq_top
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact ⟨q.X i, hi, q.presentation i, hq.isFinite_presentation i⟩

/-- **The first clause of [Stacks, Tag 01CQ].** Let `(Y, 𝒪_Y)` be a ringed space and let `F`,
`G` be `𝒪_Y`-modules with `F` of finite presentation. Then `SheafHom(F, G)` is *locally a kernel
of a map between finite direct sums of copies of `G`*: every point of `Y` has an open
neighbourhood `U` for which `SheafHom(F, G)|_U` is the kernel of a morphism
`∐_{i < m} G|_U ⟶ ∐_{j < n} G|_U`. -/
@[stacks 01CQ "local kernel presentation"]
theorem exists_locally_isoKernel_sheafInternalHom
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [F.IsFinitePresentation] (y : Y) :
    ∃ U : Opens Y, y ∈ U ∧ ∃ (m n : ℕ)
      (f : (∐ fun _ : Fin m => G.over U) ⟶ (∐ fun _ : Fin n => G.over U)),
      Nonempty ((sheafInternalHom (spaceRingedSite O) F G).over U ≅ kernel f) := by
  obtain ⟨U, hyU, P, hP⟩ := exists_isFinite_presentation_of_mem O F y
  obtain ⟨m, n, f, ⟨e⟩⟩ :=
    exists_isoKernel_sheafInternalHom ((spaceRingedSite O).over U) (G.over U) P hP
  exact ⟨U, hyU, m, n, f, ⟨sheafInternalHomOverIso (spaceRingedSite O) U F G ≪≫ e⟩⟩

/-! ### The second clause: coherence of the internal Hom -/

/-- **The second clause of [Stacks, Tag 01CQ].** On a ringed space, the internal Hom from a
module of finite presentation into a coherent module is coherent. This combines the first clause
with the gluing step `Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`.

The coherence predicate here is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`; for the one of
Stacks Tag 01BW see `isCoherent_sheafInternalHom'`, which is the same
statement and is deliberately left untagged so that the tag is not counted twice. -/
@[stacks 01CQ "coherence of internal Hom"]
theorem isCoherent_sheafInternalHom
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [F.IsFinitePresentation] [Stacks.SheafOfModules.IsCoherent G] :
    Stacks.SheafOfModules.IsCoherent
      (sheafInternalHom (spaceRingedSite O) F G) :=
  Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct (G := G)
    (exists_locally_isoKernel_sheafInternalHom O F G)

/-- **The second clause of [Stacks, Tag 01CQ]**, for the coherence predicate of
Stacks Tag 01BW. The two predicates agree by
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff`. -/
theorem isCoherent_sheafInternalHom'
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [F.IsFinitePresentation] [_root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent
      (sheafInternalHom (spaceRingedSite O) F G) :=
  have := Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
    (inferInstance : _root_.SheafOfModules.IsCoherent G)
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_of_stacks (isCoherent_sheafInternalHom O F G)

/-- **The internal Hom from a module of finite presentation into a coherent module is of finite
presentation.** This is the second clause of [Stacks, Tag 01CQ] followed by Stacks 01BW (1), and
it is the form in which [Stacks, Tag 01Y2] is consumed: on a locally Noetherian scheme the
structure sheaf is coherent, so the dual `F^∨ = SheafHom(F, 𝒪_X)` of a coherent module is of
finite presentation. -/
theorem isFinitePresentation_sheafInternalHom
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [F.IsFinitePresentation] [_root_.SheafOfModules.IsCoherent G] :
    (sheafInternalHom (spaceRingedSite O) F G).IsFinitePresentation :=
  have := isCoherent_sheafInternalHom' O F G
  _root_.isFinitePresentation_of_isCoherent _

end Local

end Stacks.SheafOfModules.InternalHom

end

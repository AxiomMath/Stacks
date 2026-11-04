module

public import StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Reduction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom out of a finitely presented module is locally a kernel

Let `(X, 𝒪_X)` be a ringed space, let `F` be a sheaf of `𝒪_X`-modules of finite presentation
and let `G` be any sheaf of `𝒪_X`-modules.  [Stacks, Tag
01CQ](https://stacks.math.columbia.edu/tag/01CQ) asserts that `SheafHom(F, G)` is, around every
point, isomorphic to the kernel of a morphism `G|_U^{⊕m} ⟶ G|_U^{⊕n}`, and deduces that
`SheafHom(F, G)` is coherent as soon as `G` is.

Both assertions are proved here.  The second is immediate from the first by
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`, whose hypothesis is the
first assertion character for character.

The proof is the source's.  Over an open on which `F` has a finite presentation
`𝒪^{⊕n} ⟶ 𝒪^{⊕m} ⟶ F ⟶ 0`, internal Hom against `G` turns the presentation into an exact
sequence `0 ⟶ Hom(F, G) ⟶ Hom(𝒪^{⊕m}, G) ⟶ Hom(𝒪^{⊕n}, G)`, because internal Hom carries
colimits in its first variable to limits
(`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`); and
`Hom(𝒪^{⊕m}, G) = G^{⊕m}`, because internal Hom out of the unit is the identity and a finite
coproduct in the first variable becomes a finite product, which in an additive category is the
same coproduct.

## Main definitions

* `unitSheafInternalHomNatIso`: internal Hom out of the unit sheaf of modules is the identity
  functor, **as a natural isomorphism**.
* `freeSheafInternalHomIso`: `Hom(𝒪^{⊕I}, G) ≅ G^{⊕I}` for a finite index type.
* `sheafInternalHomPresentationKernel`: for a global presentation of `F`, `Hom(F, G)` is the
  kernel of the induced map between the internal Homs of the two free modules.
* `sheafInternalHomOverIso`: `Hom(F, G)|_U ≅ Hom(F|_U, G|_U)`, the Stacks 0E8H
  isomorphism read through `sheafInternalHomObj`.

## Main results

* `exists_kernelPresentation_of_presentation`: the local kernel presentation over one object of
  a ringed site, given a finite presentation of `F` there.
* `exists_local_kernelPresentation`: **Stacks 01CQ, first assertion** — on the opens of a
  topological space, `Hom(F, G)` is around every point the kernel of a map
  `G|_U^{⊕m} ⟶ G|_U^{⊕n}`.
* `sheafHom_locallyKernelFiniteCoproduct`: the same for a ringed space, in the vocabulary of
  `Stacks.SheafOfModules.sheafHom`.
* `sheafHom_isCoherent`: **Stacks 01CQ, second assertion** — `SheafHom(F, G)` is coherent when
  `G` is.
* `isLocallyStructureKernel_dualSheaf`: the dual of a finitely presented module on a scheme
  satisfies `Stacks.AlgebraicGeometry.InternalHomCoherent.IsLocallyStructureKernel`, which is
  the single standing hypothesis of the Tag 0EBH adjunction.
* `reflexiveHullAdjunction`: **Stacks 0EBH** — on an integral locally Noetherian scheme the
  double-dual functor is left adjoint to the inclusion of coherent reflexive modules, with no
  remaining hypothesis.

## Implementation notes

**Internal Hom out of the unit is obtained from uniqueness of adjoints, not by hand.** Tensoring
by the unit is the identity (`MonoidalCategory.leftUnitorNatIso`), tensoring by `F` is left
adjoint to internal Hom out of `F` (the sheaf clause of Stacks 03EO,
`Stacks.SheafOfModules.InternalHom.reseatedTensorLeftAdjunction`), and a left adjoint determines
its right adjoint up to canonical isomorphism.  So `Hom(𝒪, -) ≅ 𝟭` is four lines.  Writing the
evaluation and coevaluation maps out instead forces nine `Module` instance synthesis problems
over `((restrFun 𝒪 U).obj G).obj V`, which fail because `restrFun`, `ORestr` and `Over.mk` are
semireducible; that is the one place a `backward.isDefEq.respectTransparency` escape was needed
on this route, and going through the adjunction removes it entirely.

**The two coherence classes.** `SheafOfModules.IsCoherent`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`), which is what
dot notation `F.IsCoherent` resolves to,
and `Stacks.SheafOfModules.IsCoherent`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`), which is what the locality
theory concludes, are distinct constants with identical fields, and instance search crosses
neither direction.  `isCoherent_of_isCoherent_stacks` and `isCoherent_stacks_of_isCoherent`
below are the crossing for a general ringed space; the existing
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'` pair does the same job
only for `X : Scheme`.

**Universes.** Everything is equi-universe: the site has objects in `Type u` and morphisms in
`Type u`, the structure sheaf is `CommRingCat.{u}`-valued and the modules are
`SheafOfModules.{u}`.  This is forced by the coherence substrate
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean`) and by the monoidal
structure on sheaves of modules, both of which are stated that way.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.InternalHom

namespace Stacks.AlgebraicGeometry.InternalHomLocalKernel

universe u

/-! ### Internal Hom out of the unit -/

section Unit

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor

/-- **Internal Hom out of the unit sheaf of modules is the identity functor.**

Tensoring by the unit is the identity, tensoring by `F` is left adjoint to internal Hom out of
`F`, and a left adjoint determines its right adjoint. -/
noncomputable def unitSheafInternalHomNatIso :
    internalHomSecondFunctor.{u, u, u, u} J O (𝟙_ _) ≅ 𝟭 _ :=
  (reseatedTensorLeftAdjunction O (𝟙_ _)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso _).symm)

/-- `Hom(𝒪, G) ≅ G`: internal Hom out of the unit sheaf of modules, at an object. -/
noncomputable def unitSheafInternalHomIso
    (G : _root_.SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf O)) :
    sheafInternalHomObj J O (_root_.SheafOfModules.unit _) G ≅ G :=
  eqToIso (congrArg (fun F => sheafInternalHomObj J O F G)
      (_root_.SheafOfModules.tensorUnit_sheafTensor O).symm) ≪≫
    (unitSheafInternalHomNatIso O).app G

end Unit

/-! ### Internal Hom out of a finite free module, and out of a finite presentation -/

section Presentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (G : _root_.SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf O))

/-- **`Hom(𝒪^{⊕I}, G) ≅ G^{⊕I}` for a finite index type.**

`free I` is the coproduct of copies of the unit, internal Hom carries that coproduct in the
first variable to a product, internal Hom out of the unit is the identity, and a finite product
in an additive category is the corresponding coproduct. -/
noncomputable def freeSheafInternalHomIso (I : Type u) [Finite I] :
    sheafInternalHomObj J O (_root_.SheafOfModules.free I) G ≅ ∐ (fun _ : I => G) := by
  classical
  letI := Fintype.ofFinite I
  letI : HasBiproduct (fun _ : I => G) := HasBiproduct.of_hasProduct _
  let H := sheafInternalHomFunctor J O G
  exact (PreservesCoproduct.iso H (fun _ : I => _root_.SheafOfModules.unit _)).unop.symm ≪≫
    (opProductIsoCoproduct (fun _ : I =>
      sheafInternalHomObj J O (_root_.SheafOfModules.unit _) G)).unop ≪≫
    Pi.mapIso (fun _ => unitSheafInternalHomIso O G) ≪≫
    (biproduct.isoProduct (fun _ : I => G)).symm ≪≫
    biproduct.isoCoproduct (fun _ : I => G)

/-- **Internal Hom out of a presented module is a kernel.**

A presentation of `F` exhibits `F` as the cokernel of
`free relations ⟶ kernel generators.π ⟶ free generators`, and internal Hom against `G` carries
that cokernel to a kernel. -/
noncomputable def sheafInternalHomPresentationKernel
    {F : _root_.SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf O)} (P : F.Presentation) :
    sheafInternalHomObj J O F G ≅
      kernel (sheafInternalHomObjMapLeft J O (G := G)
        (P.relations.π ≫ kernel.ι P.generators.π)) := by
  let a := P.relations.π ≫ kernel.ι P.generators.π
  let b := P.generators.π
  have hab : a ≫ b = 0 := by simp [a, b]
  let S := ShortComplex.mk a b hab
  have he : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have h : kernel.lift b a hab = P.relations.π := by
      apply (cancel_mono (kernel.ι b)).1
      rw [kernel.lift_ι]
    rw [h]
    infer_instance
  let H := sheafInternalHomFunctor J O G
  have : H.PreservesZeroMorphisms := ⟨by
    intro A B
    apply Quiver.Hom.unop_inj
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    refine _root_.PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    change f.app V 0 = 0
    exact map_zero _⟩
  let c := isColimitCoforkMapOfIsColimit' H hab he.gIsCokernel
  let k := CokernelCofork.IsColimit.ofπUnop _ _ c
  exact k.conePointUniqueUpToIso (limit.isLimit _)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Internal Hom out of a finitely presented module is a kernel of a map between finite direct
sums of copies of the target.** -/
theorem exists_kernel_of_presentation
    {F : _root_.SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf O)} (P : F.Presentation)
    (hP : P.IsFinite) :
    ∃ m n : ℕ, ∃ f : (∐ (fun _ : Fin m => G)) ⟶ (∐ (fun _ : Fin n => G)),
      Nonempty (sheafInternalHomObj J O F G ≅ kernel f) := by
  classical
  let _ := hP
  let a := P.relations.π ≫ kernel.ι P.generators.π
  let iso (I : Type u) [Finite I] :=
    letI := Fintype.ofFinite I
    freeSheafInternalHomIso O G I ≪≫ Sigma.reindex (Fintype.equivFin I) (fun _ => G)
  refine ⟨_, _, (iso P.generators.I).inv ≫ sheafInternalHomObjMapLeft J O (G := G) a ≫
    (iso P.relations.I).hom, ⟨sheafInternalHomPresentationKernel O G P ≪≫ ?_⟩⟩
  exact kernel.mapIso _ _ (iso _) (iso _) (by simp [a])

end Presentation

/-! ### Restriction to a localized site, and the colimit preservation without hypotheses -/

section RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- For a fixed target `G`, the internal Hom of sheaves of modules over a ringed site takes
colimits in the first variable to limits.  This is the ringed-site instance form of
`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`, which
carries the Stacks 03EN tag over an arbitrary site; its
`J.HasSheafCompose (forget₂ CommRingCat RingCat)` hypothesis is discharged here by
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`, so that instance search finds
the conclusion in the vocabulary the rest of this file works in. -/
@[sga "4 IV 12.2" "partial, special case"]
noncomputable instance preservesColimitsOfShape_sheafInternalHomFunctor
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (I : Type*) [Category I] :
    PreservesColimitsOfShape I (sheafInternalHomFunctor X.J X.O G) :=
  letI := X.hasSheafCompose_forget₂_ringCat
  sheafInternalHomFunctor_preservesColimitsOfShape X.J X.O G I

/-- **`Hom(F, G)|_U ≅ Hom(F|_U, G|_U)`.** This is Stacks 0E8H
(`Stacks.SheafOfModules.InternalHom.internalHomOverIso`), read through `sheafInternalHomObj`
on both sides: restriction of a sheaf of modules is restriction of its underlying presheaf of
modules, and the forgetful functor is fully faithful. -/
noncomputable def sheafInternalHomOverIso (U : X.C)
    (F G : _root_.SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafInternalHomObj X.J X.O F G).over U ≅
      sheafInternalHomObj (X.J.over U) (X.O.over U) (F.over U) (G.over U) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso (internalHomOverIso X U F G)

end RingedSite

/-! ### The local statement on a topological space -/

section Opens

variable {Y : Type u} [TopologicalSpace Y]

/-- A sheaf of modules of finite presentation has, around every point, a neighbourhood over
which it admits a finite presentation. -/
theorem exists_local_presentation {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    (F : _root_.SheafOfModules.{u} R) (hF : F.IsFinitePresentation) (x : Y) :
    ∃ U : Opens Y, x ∈ U ∧ ∃ P : (F.over U).Presentation, P.IsFinite := by
  obtain ⟨⟨q, hq⟩⟩ := hF
  have hx : x ∈ iSup q.X := by rw [(Opens.coversTop_iff Y q.X).mp q.coversTop]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨q.X i, hi, q.presentation i, hq.isFinite_presentation i⟩

variable (𝒪 : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology Y)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- The structure sheaf of a ringed space, packaged as a sheaf of *commutative* rings on the
site of its opens. `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is the same datum
with commutativity forgotten. -/
def commRingSheaf : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u} :=
  ⟨𝒪, (Presheaf.isSheaf_iff_isSheaf_comp _ 𝒪 (forget₂ CommRingCat.{u} RingCat.{u})).mpr h𝒪⟩

/-- `Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
`SheafOfModules.Tensor.ringSheaf` are the same sheaf of rings. -/
theorem structureSheaf_eq_ringSheaf :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪 =
      SheafOfModules.Tensor.ringSheaf (commRingSheaf 𝒪 h𝒪) := rfl

/-- `Stacks.SheafOfModules.sheafHom` is the internal Hom sheaf of
`Stacks.SheafOfModules.InternalHom.sheafInternalHomObj`. -/
theorem sheafHom_eq_sheafInternalHomObj
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) :
    _root_.Stacks.SheafOfModules.sheafHom 𝒪 h𝒪 F G =
      sheafInternalHomObj (Opens.grothendieckTopology Y) (commRingSheaf 𝒪 h𝒪) F G := rfl

/-- The ringed site of the opens of a topological space with the given structure sheaf. -/
def ringedSiteOfOpens : RingedSite.{u, u, u} where
  C := Opens Y
  J := Opens.grothendieckTopology Y
  O := commRingSheaf 𝒪 h𝒪

/-- **Stacks 01CQ, first assertion.** The sheaf Hom out of a sheaf of modules of finite
presentation is, around every point, isomorphic to the kernel of a morphism between two finite
direct sums of copies of the target. -/
theorem exists_local_kernel_sheafHom
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪))
    (hF : F.IsFinitePresentation) (x : Y) :
    ∃ U : Opens Y, x ∈ U ∧ ∃ m n : ℕ,
      ∃ f : (∐ (fun _ : Fin m => G.over U)) ⟶ (∐ (fun _ : Fin n => G.over U)),
        Nonempty ((_root_.Stacks.SheafOfModules.sheafHom 𝒪 h𝒪 F G).over U ≅ kernel f) := by
  obtain ⟨U, hx, P, hP⟩ := exists_local_presentation F hF x
  obtain ⟨m, n, f, ⟨e⟩⟩ :=
    exists_kernel_of_presentation ((commRingSheaf 𝒪 h𝒪).over U) (G.over U) P hP
  exact ⟨U, hx, m, n, f,
    ⟨sheafInternalHomOverIso (ringedSiteOfOpens 𝒪 h𝒪) U F G ≪≫ e⟩⟩

/-- **Stacks 01CQ, second assertion**, for `Stacks.SheafOfModules.IsCoherent`.

This is `Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct` fed with the first
assertion, whose statement is its hypothesis character for character. -/
theorem isCoherent_sheafHom
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪))
    (hF : F.IsFinitePresentation)
    (hG : _root_.Stacks.SheafOfModules.IsCoherent G) :
    _root_.Stacks.SheafOfModules.IsCoherent
      (_root_.Stacks.SheafOfModules.sheafHom 𝒪 h𝒪 F G) :=
  let := hG
  _root_.Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct
    (exists_local_kernel_sheafHom 𝒪 h𝒪 F G hF)

end Opens

/-! ### The two coherence classes -/

section CoherenceCrossing

variable {Y : Type u} [TopologicalSpace Y]
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- `Stacks.SheafOfModules.IsCoherent` implies `SheafOfModules.IsCoherent`, which is what dot
notation resolves to.  The two are distinct constants with identical fields, and instance
search crosses neither direction. -/
theorem isCoherent_of_isCoherent_stacks {M : _root_.SheafOfModules.{u} R}
    (h : _root_.Stacks.SheafOfModules.IsCoherent M) : M.IsCoherent :=
  ⟨h.1, h.2⟩

/-- The converse crossing of `isCoherent_of_isCoherent_stacks`. -/
theorem isCoherent_stacks_of_isCoherent {M : _root_.SheafOfModules.{u} R}
    (h : M.IsCoherent) : _root_.Stacks.SheafOfModules.IsCoherent M :=
  ⟨h.1, h.2⟩

end CoherenceCrossing

/-! ### Stacks 01CQ for a ringed space -/

section RingedSpace

variable (X : RingedSpace.{u, u})

/-- **Stacks 01CQ, first assertion, for a ringed space.** A sheaf Hom from a finitely presented
module is locally the kernel of a map between finite direct sums of copies of the target. -/
@[stacks 01CQ "local kernel presentation"]
theorem sheafHom_locallyKernelFiniteCoproduct
    (F G : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    [F.IsFinitePresentation] :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ m n : ℕ,
        ∃ f : (∐ (fun _ : Fin m => G.over U)) ⟶ (∐ (fun _ : Fin n => G.over U)),
          Nonempty ((_root_.Stacks.SheafOfModules.sheafHom X.presheaf
              (structureSheafRing X).property F G).over
                U ≅
            (kernel f :
              _root_.SheafOfModules.{u}
                ((structureSheafRing X).over U))) :=
  fun x => exists_local_kernel_sheafHom X.presheaf
    (structureSheafRing X).property F G
      ‹F.IsFinitePresentation› x

/-- **Stacks 01CQ, second assertion, for a ringed space.** Internal Hom from a finitely
presented module into a coherent module is coherent. -/
@[stacks 01CQ "coherence of internal Hom"]
theorem sheafHom_isCoherent
    (F G : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    [F.IsFinitePresentation] [G.IsCoherent] :
    (_root_.Stacks.SheafOfModules.sheafHom X.presheaf
      (structureSheafRing X).property F G).IsCoherent
        :=
  isCoherent_of_isCoherent_stacks
    (isCoherent_sheafHom X.presheaf (structureSheafRing
      X).property F G
      ‹F.IsFinitePresentation› (isCoherent_stacks_of_isCoherent ‹G.IsCoherent›))

end RingedSpace

/-! ### Stacks 0EBH -/

section Scheme

open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.InternalHomCoherent

variable {X : Scheme.{u}}

/-- **The dual of a finitely presented module on a scheme is locally the kernel of a map between
finite direct sums of copies of the structure sheaf.**

This is Stacks 01CQ's first assertion at target the structure sheaf, in the form
`Stacks.AlgebraicGeometry.InternalHomCoherent.IsLocallyStructureKernel` wants it: the dual
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf F` *is* the sheaf Hom `Hom(F, 𝒪_X)`. -/
theorem isLocallyStructureKernel_dualSheaf (F : X.Modules)
    (hF : F.IsFinitePresentation) : IsLocallyStructureKernel (dualSheaf F) :=
  exists_local_kernel_sheafHom X.presheaf X.ringCatSheaf.property F
    (_root_.SheafOfModules.unit X.ringCatSheaf) hF

/-- **The dual of a coherent module on a scheme is locally the kernel of a map between finite
direct sums of copies of the structure sheaf.**

A coherent module over any ringed space is of finite presentation, by Stacks 01BW (1). -/
theorem isLocallyStructureKernel_dualSheaf_of_isCoherent (F : X.Modules) (hF : F.IsCoherent) :
    IsLocallyStructureKernel (dualSheaf F) :=
  let := hF
  isLocallyStructureKernel_dualSheaf F (isFinitePresentation_of_isCoherent F)

/-- **The dual of a coherent module on a locally Noetherian scheme is coherent.**

This is Tag 0EBH's single standing hypothesis, discharged at Tag 0EBH's own hypotheses. -/
theorem isCoherent_dualSheaf [IsLocallyNoetherian X] (F : X.Modules) (hF : F.IsCoherent) :
    (dualSheaf F).IsCoherent :=
  isCoherent_dualSheaf_of_isLocallyStructureKernel F
    (isLocallyStructureKernel_dualSheaf_of_isCoherent F hF)

/-- **Stacks Tag 0EBH.** On an integral locally Noetherian scheme the double-dual functor is
left adjoint to the inclusion of coherent reflexive modules into coherent modules, with the
canonical bidual map as its unit.

This is `reflexiveHullAdjunction_of_isLocallyStructureKernel` with its standing hypothesis
discharged by `isLocallyStructureKernel_dualSheaf_of_isCoherent`. -/
@[stacks 0EBH "adjunction"]
noncomputable def reflexiveHullAdjunction (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] :
    { p : (Σ L : ReflexiveHull.CoherentModules X ⥤ ReflexiveHull.CoherentReflexiveModules X,
        L ⊣ ReflexiveHull.inclusion X) //
      ∀ F : ReflexiveHull.CoherentModules X,
        ∃ e : (p.1.obj F).obj.obj = ReflexiveModules.reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom e =
            (ReflexiveModules.toReflexiveHull F.obj).1 } :=
  reflexiveHullAdjunction_of_isLocallyStructureKernel X
    fun G hG => isLocallyStructureKernel_dualSheaf_of_isCoherent G hG

end Scheme

end Stacks.AlgebraicGeometry.InternalHomLocalKernel

end

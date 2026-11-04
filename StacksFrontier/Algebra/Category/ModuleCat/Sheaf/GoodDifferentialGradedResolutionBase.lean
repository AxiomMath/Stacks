module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolution

/-!
# The base of a flat resolution: the free module on the closed sections

Let `(C, J)` be a site, let `R` be a sheaf of rings on it, let `D` be a sheaf of differential
graded `R`-algebras and let `M` be a right differential graded `D`-module. This file builds the
first stage of the tower of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionColimit.lean`:
a sheaf of graded sets made out of the closed sections of `M`, the free differential graded
module on it, and the homomorphism to `M` which is surjective on cohomology.

## Main definitions

* `SheafOfModules.ClosedSection K V` is a local section over `V` of the sheaf of graded sets of
  closed sections: a degree — a section of the constant sheaf of integers, so a *locally*
  constant integer — together with a cocycle of `M` in every degree.
* `SheafOfModules.closedSections K` is that sheaf of graded sets, for `K` any cochain
  complex of sheaves of modules: nothing of the module structure of `M` enters it, which is what
  lets the left-handed resolution reuse it.
* `SheafOfModules.cycleSection M.complex n V ξ` is the local section of degree `n` carrying a given
  cocycle `ξ` of degree `n`: every cocycle of `M` names a generator.
* `SheafOfModules.closedSectionsFamily M` is the family of homogeneous generators it carries:
  the generator attached to a local section of degree `n` is its degree-`n` cocycle, included
  into `M^n`. Every one of them is closed, by `SheafOfModules.closedSectionsFamily_closed`.
* `SheafOfModules.freeOnClosedSectionsHom M` is the resulting homomorphism of *differential*
  graded modules `D[Z(M)] ⟶ M`, obtained from `SheafOfModules.dgLiftHom`.

## Main results

* `SheafOfModules.exists_cycles_section`: a section of `K^n` killed by the differential is the
  image of a section of the cocycle sheaf `K.cycles n`. Taking sections over an object of the
  site is left exact, and `K.cycles n` is a kernel of the differential.
* `SheafOfModules.epi_cyclesMap_of_exists_closed_preimage`: a morphism of cochain complexes of
  sheaves of modules which is surjective on the sections killed by the differentials is an
  epimorphism on the cocycle sheaves.
* `SheafOfModules.exists_closed_preimage_freeOnClosedSectionsHom`: every section of `M^n` killed
  by the differential is the image of a section of `D[Z(M)]^n` killed by the differential, namely
  of the generator it names.
* `SheafOfModules.epi_homologyMap_freeOnClosedSectionsHom`: **`Hⁿ(D[Z(M)]) ⟶ Hⁿ(M)` is an
  epimorphism for every `n`**, which is the `hepi` hypothesis of
  `SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`.

## Implementation notes

**Why the degree is carried by a locally constant integer and a cocycle in every degree.** The
sheaf of graded sets named in the first proof of Tag 0FSH is `∐ₙ Ker(d^n)`, the coproduct over
the degrees of the cocycle sheaves. The pointwise disjoint union `V ↦ Σ n, Ker(d^n)(V)` is *not*
a sheaf: over an object covered by two disjoint pieces, a cocycle of degree `0` on one and a
cocycle of degree `1` on the other is a compatible family with no amalgamation. What is a sheaf
— and what `SheafOfModules.ClosedSection` is — is a section of the constant sheaf of integers,
which is the locally constant degree, together with a cocycle in each degree. No sheafification
is involved, so a local section of degree `n` has an honest degree-`n` cocycle attached to it
(`SheafOfModules.ClosedSection.cyc`), which is what makes the family of generators below
writable and its surjectivity provable; the degree-`n` part of a sheaf of graded sets built by
sheafifying the disjoint union carries no such section without an identification of the fibre of
a sheafification, which this development does not have.

This sheaf is *larger* than `∐ₙ Ker(d^n)`, which sits inside it as the subsheaf of those pairs
whose degree-`k` cocycle vanishes locally wherever the degree is not `k`; no condition of that
kind is imposed here, so the degree-`n` part of `SheafOfModules.closedSections M.complex`
retains the cocycles in the other degrees as well. Nothing below needs it to be
`∐ₙ Ker(d^n)` on the nose:
what the resolution uses is that every generator goes to a cocycle of `M`
(`SheafOfModules.closedSectionsFamily_closed`) and that every cocycle of `M` is the image of a
generator (`SheafOfModules.cycleSection`), and the free module on a sheaf of graded sets is flat
and K-flat whatever that sheaf is (Tag 0FSG, `SheafOfModules.freeDGModule_isGradedFlat` and
`SheafOfModules.freeDGModule_isKFlat`). The extra generators only make `D[Z(M)]` bigger.

**The cocycle sheaf is Mathlib's.** `Ker(d^n)` is `HomologicalComplex.cycles`, with
`HomologicalComplex.iCycles` for the inclusion; `SheafOfModules R` is abelian, so this is
available with no further hypotheses. The degree parts of a sheaf of graded sets are sheaves of
*sets*, so what enters `SheafOfModules.ClosedSection` is the underlying sheaf of sets of
`M.complex.cycles n`, i.e. its sections with the module structure forgotten; the sheaf condition
in that form is `Stacks.setSheaf`.

**Surjectivity on cohomology comes from surjectivity on cocycle sections.** Every cocycle of `M`
over `V` is, by construction, the image of a generator of `D[Z(M)]`, and that generator is a
cocycle of `D[Z(M)]` (`SheafOfModules.freeDGModule_d_freeGenerator`). Since taking sections over
an object of the site is left exact, cocycle sheaves are computed sectionwise, so
`Z^n(D[Z(M)]) ⟶ Z^n(M)` is an epimorphism; composing with the epimorphism `Z^n(M) ⟶ Hⁿ(M)` and
cancelling gives that `Hⁿ(D[Z(M)]) ⟶ Hⁿ(M)` is one.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Sections of a cocycle sheaf

The cocycle sheaf `K.cycles n` of a cochain complex of sheaves of modules is a kernel of the
differential, and taking sections over an object of the site is left exact, so its sections are
exactly the sections killed by the differential. -/

section Cycles

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- The inclusion of the cocycle sheaf is injective on sections: it is a monomorphism, and
taking sections over an object of the site is left exact. -/
theorem injective_iCycles_sections (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ)
    (U : Cᵒᵖ) : Function.Injective (homSections (K.iCycles n) U) :=
  injective_of_mono_sections (K.iCycles n) inferInstance U

/-- **A section killed by the differential is a section of the cocycle sheaf.** The cocycle
sheaf is a kernel of the differential and the functor taking sections over an object of the site
preserves finite limits, so it carries that kernel to the kernel of the map on sections. -/
theorem exists_cycles_section (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.X n).val.obj U) (hx : homSections (K.d n (n + 1)) U x = 0) :
    ∃ ξ : (K.cycles n).val.obj U, homSections (K.iCycles n) U ξ = x := by
  let E := SheafOfModules.forget.{m} R ⋙ PresheafOfModules.evaluation R.obj U
  have hpl : PreservesLimit (parallelPair (K.d n (n + 1)) 0) E :=
    PreservesFiniteLimits.preservesFiniteLimits _ |>.preservesLimit
  have hker : IsLimit ((KernelFork.ofι (K.iCycles n) (K.iCycles_d n (n + 1))).map E) :=
    KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) E
  have hzero : E.map (K.iCycles n) ≫ E.map (K.d n (n + 1)) = 0 := by
    rw [← E.map_comp, K.iCycles_d, E.map_zero]
  exact (ShortComplex.moduleCat_exact_iff
    (ShortComplex.mk (E.map (K.iCycles n)) (E.map (K.d n (n + 1))) hzero)).mp
    (ShortComplex.exact_of_f_is_kernel _ hker) x hx

/-- A cocycle, included into the terms of the complex, is killed by the differential. -/
private theorem homSections_d_iCycles (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ)
    (U : Cᵒᵖ) (ξ : (K.cycles n).val.obj U) :
    homSections (K.d n (n + 1)) U (homSections (K.iCycles n) U ξ) = 0 :=
  ((homSections_comp (K.iCycles n) (K.d n (n + 1)) U ξ).symm.trans
    (homSections_congr (K.iCycles_d n (n + 1)) U ξ)).trans (homSections_zero U ξ)

/-! ### Surjectivity on cohomology -/

/-- **A morphism of cochain complexes of sheaves of modules which is surjective on the sections
killed by the differentials is an epimorphism on the cocycle sheaves.** Cocycle sheaves are
computed sectionwise, taking sections over an object of the site being left exact, so this is
the sectionwise surjectivity of the hypothesis. -/
theorem epi_cyclesMap_of_exists_closed_preimage
    {K L : CochainComplex (SheafOfModules.{m} R) ℤ} (φ : K ⟶ L) (n : ℤ)
    (h : ∀ (U : Cᵒᵖ) (x : (L.X n).val.obj U), homSections (L.d n (n + 1)) U x = 0 →
      ∃ y : (K.X n).val.obj U, homSections (K.d n (n + 1)) U y = 0 ∧
        homSections (φ.f n) U y = x) :
    Epi (HomologicalComplex.cyclesMap φ n) := by
  refine DifferentialGradedModule.epi_of_surjective_sections _ fun U ξ => ?_
  obtain ⟨y, hdy, hy⟩ := h U _ (homSections_d_iCycles L n U ξ)
  obtain ⟨η, hη⟩ := exists_cycles_section K n U y hdy
  refine ⟨η, injective_iCycles_sections L n U ?_⟩
  calc homSections (L.iCycles n) U (homSections (HomologicalComplex.cyclesMap φ n) U η)
      = homSections (HomologicalComplex.cyclesMap φ n ≫ L.iCycles n) U η :=
        (homSections_comp _ _ U η).symm
    _ = homSections (K.iCycles n ≫ φ.f n) U η :=
        homSections_congr (HomologicalComplex.cyclesMap_i φ n) U η
    _ = homSections (φ.f n) U (homSections (K.iCycles n) U η) := homSections_comp _ _ U η
    _ = homSections (φ.f n) U y := congrArg (fun z => homSections (φ.f n) U z) hη
    _ = homSections (L.iCycles n) U ξ := hy

/-- A morphism of cochain complexes which is an epimorphism on the cocycle sheaves is an
epimorphism on cohomology: cohomology is a quotient of the cocycles. -/
theorem epi_homologyMap_of_epi_cyclesMap {K L : CochainComplex (SheafOfModules.{m} R) ℤ}
    (φ : K ⟶ L) (n : ℤ) (hφ : Epi (HomologicalComplex.cyclesMap φ n)) :
    Epi (HomologicalComplex.homologyMap φ n) := by
  have : Epi (K.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
    rw [HomologicalComplex.homologyπ_naturality]
    exact epi_comp _ _
  exact epi_of_epi (K.homologyπ n) _

end Cycles

/-! ### The sheaf of graded sets of closed sections -/

section ClosedSections

variable [HasWeakSheafify J (Type m)] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{m}] {D : DifferentialGradedAlgebra.{t, m} R}

/-- The constant sheaf of integers, the target of the degree morphism of a sheaf of graded
sets. -/
noncomputable abbrev intSheaf (J : GrothendieckTopology C) [HasWeakSheafify J (Type m)] :
    Sheaf J (Type m) :=
  (constantSheaf J (Type m)).obj (ULift.{m} ℤ)

/-- The constant section of the sheaf of integers with value `n`: the degree that a local
section of a sheaf of graded sets has when it is homogeneous of degree `n`. -/
noncomputable abbrev intSection (V : Cᵒᵖ) (n : ℤ) : (intSheaf J).obj.obj V :=
  (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{m} ℤ))).app V ⟨n⟩

/-- **A local section over `V` of the sheaf of graded sets of closed sections of `K`**: a
degree, which is a section of the constant sheaf of integers and so a locally constant integer,
together with a cocycle of `K` over `V` in every degree. See the implementation notes of this
file for why the degree is not a single integer and why the cocycles in the degrees other than
the one carried are kept. -/
structure ClosedSection (K : CochainComplex (SheafOfModules.{m} R) ℤ) (V : Cᵒᵖ) : Type m where
  /-- The degree, as a section of the constant sheaf of integers. -/
  deg : (intSheaf J).obj.obj V
  /-- The cocycle of `K` over `V` in degree `n`. -/
  cyc (n : ℤ) : (K.cycles n).val.obj V

/-- Two local sections of the sheaf of graded sets of closed sections agree as soon as their
degrees and all their cocycles do. -/
@[ext] theorem ClosedSection.ext {K : CochainComplex (SheafOfModules.{m} R) ℤ} {V : Cᵒᵖ}
    {s s' : ClosedSection K V} (hdeg : s.deg = s'.deg)
    (hcyc : ∀ n : ℤ, s.cyc n = s'.cyc n) : s = s' := by
  cases s
  cases s'
  simp_all only [ClosedSection.mk.injEq, true_and]
  exact funext hcyc

/-- Restriction of a local section of the sheaf of graded sets of closed sections: the degree
and every cocycle are restricted. -/
noncomputable def ClosedSection.restrict {K : CochainComplex (SheafOfModules.{m} R) ℤ} {V W : Cᵒᵖ}
    (f : V ⟶ W) (s : ClosedSection K V) : ClosedSection K W where
  deg := (intSheaf J).obj.map f s.deg
  cyc n := Stacks.sectionRestrict (K.cycles n).val f (s.cyc n)

/-- The presheaf of graded sets of closed sections of `K`. -/
noncomputable def closedPresheaf (K : CochainComplex (SheafOfModules.{m} R) ℤ) : Cᵒᵖ ⥤ Type m where
  obj V := ClosedSection K V
  map f := TypeCat.ofHom (ClosedSection.restrict f)
  map_id V := by
    ext s
    · exact (intSheaf J).obj.map_id_apply V s.deg
    · exact Stacks.sectionRestrict_id (K.cycles _).val V (s.cyc _)
  map_comp f g := by
    ext s
    · exact (intSheaf J).obj.map_comp_apply f g s.deg
    · exact Stacks.sectionRestrict_comp (K.cycles _).val f g (s.cyc _)

/-- **The presheaf of graded sets of closed sections is a sheaf.** A compatible family of local
sections is a compatible family of degrees together with, in every degree, a compatible family
of cocycles; the constant sheaf of integers and the cocycle sheaves amalgamate those, and a
local section is determined by its components. -/
theorem isSheaf_closedPresheaf (K : CochainComplex (SheafOfModules.{m} R) ℤ) :
    Presheaf.IsSheaf J (closedPresheaf K) := by
  have hdeg : Presieve.IsSheaf J (intSheaf J).obj :=
    (isSheaf_iff_isSheaf_of_type J _).mp (intSheaf J).property
  have hcyc : ∀ n : ℤ, Presieve.IsSheaf J (Stacks.setSheaf (K.cycles n)).obj :=
    fun n => (isSheaf_iff_isSheaf_of_type J _).mp (Stacks.setSheaf (K.cycles n)).property
  rw [isSheaf_iff_isSheaf_of_type]
  intro X T hT y hy
  let ydeg : Presieve.FamilyOfElements (intSheaf J).obj T.arrows :=
    fun _ f hf => (y f hf).deg
  let ycyc : ∀ n : ℤ,
      Presieve.FamilyOfElements (Stacks.setSheaf (K.cycles n)).obj T.arrows :=
    fun n _ f hf => (y f hf).cyc n
  have hydeg : ydeg.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    exact congrArg ClosedSection.deg (hy g₁ g₂ h₁ h₂ h)
  have hycyc : ∀ n : ℤ, (ycyc n).Compatible := by
    intro n Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    exact congrArg (fun s => ClosedSection.cyc s n) (hy g₁ g₂ h₁ h₂ h)
  obtain ⟨td, htd, hud⟩ := hdeg T hT ydeg hydeg
  choose tc htc huc using fun n : ℤ => hcyc n T hT (ycyc n) (hycyc n)
  exact ⟨⟨td, tc⟩, fun Y f hf => ClosedSection.ext (htd f hf) fun n => htc n f hf,
    fun t' ht' => ClosedSection.ext
      (hud t'.deg fun _ f hf => congrArg ClosedSection.deg (ht' f hf)) fun n =>
      huc n (t'.cyc n) fun _ f hf => congrArg (fun s => ClosedSection.cyc s n) (ht' f hf)⟩

/-- **The sheaf of graded sets of closed sections of `K`**, the sheaf of graded sets which plays
the part of `∐ₙ Ker(d_M^n)` in the first proof of Tag 0FSH: its degree morphism is the locally
constant degree carried by a local section, a local section of degree `n` has a cocycle of `K`
of degree `n` attached to it, and every cocycle of degree `n` is attached to one
(`SheafOfModules.cycleSection`). Its degree-`n` part is larger than `Ker(d_M^n)`; see the
implementation notes of this file, and note that nothing here needs the two to agree. -/
noncomputable def closedSections (K : CochainComplex (SheafOfModules.{m} R) ℤ) :
    Stacks.SheafOfGradedSets.{m} J where
  sheaf := ⟨closedPresheaf K, isSheaf_closedPresheaf K⟩
  degree := ⟨{ app := fun _ => TypeCat.ofHom ClosedSection.deg, naturality := fun _ _ _ => rfl }⟩

/-- A local section of `closedSections K` has degree `n` exactly when its degree is the constant
section of value `n`. -/
theorem closedSections_hasDegree_iff (K : CochainComplex (SheafOfModules.{m} R) ℤ) (V : Cᵒᵖ)
    (s : (closedSections K).sheaf.obj.obj V) (n : ℤ) :
    (closedSections K).HasDegree V s n ↔ s.deg = intSection V n :=
  Iff.rfl

/-- A cocycle of `K` of degree `n` over `V`, viewed as a local section of degree `n` of the
sheaf of graded sets of closed sections: it carries the cocycle in degree `n` and zero in the
other degrees. -/
noncomputable def cycleSection (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (ξ : (K.cycles n).val.obj V) : ClosedSection K V where
  deg := intSection V n
  cyc k := if h : n = k then castHom (fun j => K.cycles j) h V ξ else 0

/-- The degree of the local section `cycleSection K n V ξ` is the constant section of value `n`. -/
@[simp] theorem cycleSection_deg (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (ξ : (K.cycles n).val.obj V) : (cycleSection K n V ξ).deg = intSection V n := rfl

/-- The cocycle of degree `n` carried by the local section `cycleSection K n V ξ` is `ξ`. -/
@[simp] theorem cycleSection_cyc_self (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ)
    (V : Cᵒᵖ) (ξ : (K.cycles n).val.obj V) : (cycleSection K n V ξ).cyc n = ξ := by
  show (if h : n = n then castHom (fun j => K.cycles j) h V ξ else 0) = ξ
  rw [dite_eq_left rfl]
  exact castHom_rfl (fun j => K.cycles j) V ξ

/-- Every cocycle of degree `n` is the degree-`n` local section it defines. -/
theorem cycleSection_hasDegree (K : CochainComplex (SheafOfModules.{m} R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (ξ : (K.cycles n).val.obj V) :
    (closedSections K).HasDegree V (cycleSection K n V ξ) n :=
  rfl

/-! ### The free differential graded module on the closed sections -/

/-- **The family of homogeneous generators carried by the sheaf of graded sets of closed
sections**: the generator attached to a local section of degree `n` is the cocycle of degree `n`
that this local section carries, included into `M^n`. -/
noncomputable def closedSectionsFamily (M : DifferentialGradedModule.{t, m, m} D) :
    GradedGeneratorFamily (closedSections M.complex) (GradedModule.ofDifferentialGraded M) where
  app n V s _ := homSections (M.complex.iCycles n) V (s.cyc n)
  naturality := by
    intro n V W f s _ _
    exact homSections_naturality (M.complex.iCycles n) f (s.cyc n)

/-- The generator attached to a local section `s` of degree `n` of `closedSections M.complex` is
the cocycle of degree `n` it carries, included into `M^n`. -/
@[simp] theorem closedSectionsFamily_app (M : DifferentialGradedModule.{t, m, m} D) (n : ℤ)
    (V : Cᵒᵖ) (s : (closedSections M.complex).sheaf.obj.obj V)
    (hs : (closedSections M.complex).HasDegree V s n) :
    (closedSectionsFamily M).app n V s hs = homSections (M.complex.iCycles n) V (s.cyc n) :=
  rfl

/-- **Every generator carried by the sheaf of graded sets of closed sections is closed.** This
holds by construction: the generators are the cocycles of `M`. It is the hypothesis that turns
the lift of the family into a homomorphism of *differential* graded modules. -/
theorem closedSectionsFamily_closed (M : DifferentialGradedModule.{t, m, m} D) (n : ℤ)
    (V : Cᵒᵖ) (s : (closedSections M.complex).sheaf.obj.obj V)
    (hs : (closedSections M.complex).HasDegree V s n) :
    homSections (M.complex.d n (n + 1)) V ((closedSectionsFamily M).app n V s hs) = 0 :=
  homSections_d_iCycles M.complex n V (s.cyc n)

/-- **The homomorphism of differential graded modules `D[Z(M)] ⟶ M`** out of the free
differential graded module on the sheaf of graded sets of closed sections of `M`: it sends each
canonical generator to the cocycle of `M` that generator names. This is the module `P₀` of the
first proof of Tag 0FSH, built with no hypotheses. -/
noncomputable def freeOnClosedSectionsHom (M : DifferentialGradedModule.{t, m, m} D) :
    freeDGModule (closedSections M.complex) D ⟶ M :=
  dgLiftHom (closedSections M.complex) D M (closedSectionsFamily M) (closedSectionsFamily_closed M)

/-- **`D[Z(M)] ⟶ M` sends the generator named by a cocycle to that cocycle.** -/
theorem freeOnClosedSectionsHom_generator (M : DifferentialGradedModule.{t, m, m} D) (n : ℤ)
    (V : Cᵒᵖ) (ξ : (M.complex.cycles n).val.obj V) :
    homSections ((freeOnClosedSectionsHom M).toHomologicalComplex.f n) V
        (freeGeneratorSection D.toGradedAlgebra (closedSections M.complex) n V
          (cycleSection M.complex n V ξ) (cycleSection_hasDegree M.complex n V ξ)) =
      homSections (M.complex.iCycles n) V ξ :=
  (dgLiftHom_generator (closedSections M.complex) D M (closedSectionsFamily M)
      (closedSectionsFamily_closed M) n V (cycleSection M.complex n V ξ)
      (cycleSection_hasDegree M.complex n V ξ)).trans
    (congrArg (fun ζ => homSections (M.complex.iCycles n) V ζ)
      (cycleSection_cyc_self M.complex n V ξ))

/-- **Every section of `M^n` killed by the differential is the image of a section of
`D[Z(M)]^n` killed by the differential**: it is the image of the generator it names, and every
canonical generator of a free differential graded module is closed. -/
theorem exists_closed_preimage_freeOnClosedSectionsHom
    (M : DifferentialGradedModule.{t, m, m} D) (n : ℤ) (V : Cᵒᵖ)
    (x : (M.complex.X n).val.obj V) (hx : homSections (M.complex.d n (n + 1)) V x = 0) :
    ∃ y : ((freeDGModule (closedSections M.complex) D).complex.X n).val.obj V,
      homSections ((freeDGModule (closedSections M.complex) D).complex.d n (n + 1)) V y = 0 ∧
        homSections ((freeOnClosedSectionsHom M).toHomologicalComplex.f n) V y = x := by
  obtain ⟨ξ, hξ⟩ := exists_cycles_section M.complex n V x hx
  exact ⟨freeGeneratorSection D.toGradedAlgebra (closedSections M.complex) n V
      (cycleSection M.complex n V ξ) (cycleSection_hasDegree M.complex n V ξ),
    freeDGModule_d_freeGenerator (closedSections M.complex) D n V
      (cycleSection M.complex n V ξ) (cycleSection_hasDegree M.complex n V ξ),
    (freeOnClosedSectionsHom_generator M n V ξ).trans hξ⟩

/-! ### Surjectivity on cohomology -/

/-- **`Hⁿ(D[Z(M)]) ⟶ Hⁿ(M)` is an epimorphism for every `n`.** Every cohomology class of `M` is
represented by a cocycle, every cocycle of `M` is the image of a canonical generator of
`D[Z(M)]`, and that generator is itself a cocycle. This is the `hepi` hypothesis of
`SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`, for the first stage of its
tower. -/
theorem epi_homologyMap_freeOnClosedSectionsHom (M : DifferentialGradedModule.{t, m, m} D)
    (n : ℤ) :
    Epi (HomologicalComplex.homologyMap (freeOnClosedSectionsHom M).toHomologicalComplex n) :=
  epi_homologyMap_of_epi_cyclesMap _ n
    (epi_cyclesMap_of_exists_closed_preimage _ n
      (exists_closed_preimage_freeOnClosedSectionsHom M n))

end ClosedSections

end SheafOfModules

end

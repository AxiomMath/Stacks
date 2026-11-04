module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Algebra.Homology.ShortComplex.DiscreteFunctorCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an acyclic covering family on a site

Let `C` be a site, let `𝒰 = {U_i → U}` be a covering family of an object `U` and let `F` be an
abelian sheaf on `C` whose higher cohomology vanishes on every nonempty finite fibre product
`U_{i_0} ×_U ⋯ ×_U U_{i_p}` of members of the family. Then the canonical comparison
`Stacks.CechSite.cechCohomologyToCohomology` of [Stacks, Tag 03AX], from the Čech cohomology of
the family to the cohomology of `F` over `U`, is an isomorphism in every degree. This is
[Stacks, Tag 03F7].

## Main results

* `Stacks.CechSite.Acyclic.isIso_cechCohomologyToCohomology_app`: **[Stacks, Tag 03F7]** — the
  comparison `Ȟ^p(𝒰, F) ⟶ H^p(U, F)` is an isomorphism.
* `Stacks.CechSite.Acyclic.isIso_cechToDerivedSections_app`: the same before passing to
  cohomology — the Čech complex of `F` *is* `RΓ(U, F)` in the derived category.

## The argument

The comparison of [Stacks, Tag 03AX] is `Q(β) ≫ Q(α)⁻¹` followed by the identification of the
sections of an injective resolution `F ⟶ J^•` with derived sections, where

* `α : Γ(U, J^•) ⟶ Tot(Č(𝒰, J^•))` restricts sections degreewise into the degree-zero Čech
  term, and
* `β : Č(𝒰, F) ⟶ Tot(Č(𝒰, J^•))` is the Čech complex of the inclusion `F ⟶ J^0`.

Two of the three factors are invertible for every covering family and every abelian sheaf, and
are already proved with [Stacks, Tag 03AX]: `α` because the *columns* of the Čech bicomplex are
the Čech complexes of the injective sheaves `J^q`, and the last factor by the universal property
of the right derived functor. So the whole content of this tag is that `β` is a
quasi-isomorphism, i.e. that the *rows* of the Čech bicomplex of an injective resolution are
exact away from resolution degree zero with the Čech complex of `F` as their degree-zero kernel —
and that is exactly where the acyclicity hypothesis enters, through the criterion of
[Stacks, Tag 0133] applied to the flipped bicomplex.

A row of the Čech bicomplex in Čech degree `n` is the product, over the tuples
`k : Fin (n + 1) → I`, of the sections of the resolution over the fibre product selected by `k`.
Three facts make the row exact away from resolution degree zero:

* sections over one fibre product carry the resolution to a complex exact away from degree zero,
  because the higher right derived functors of that sections functor vanish on `F` — this is the
  hypothesis, read through `CategoryTheory.InjectiveResolution.isoRightDerivedObj` and the
  `ℕ`-to-`ℤ` bridge `CategoryTheory.Functor.mapExtendIso`;
* exactness in a category of functors out of a discrete category is exactness in each component,
  because evaluation preserves homology;
* products indexed by an arbitrary type are exact in `AddCommGrpCat`, which is Mathlib's
  `CategoryTheory.AB4Star` instance — so the limit functor carries the componentwise exactness to
  the product.

The kernel clause of [Stacks, Tag 0133] for the rows needs no hypothesis beyond left exactness:
the Čech cochain functor in a fixed degree preserves finite limits, being a product of sections
functors, and sections of abelian sheaves over an object preserve finite limits.

## Implementation notes

This file mirrors `StacksFrontier/Topology/Sheaves/Cohomology/CechToCohomology/AcyclicCovering.lean`,
which carries out the same argument for an open covering of a ringed space ([Stacks, Tag 01ET]),
throughout; the machinery of [Stacks, Tag 0133] it uses is the universe-polymorphic
`StacksFrontier/Algebra/Homology/TotalComplexQuasiIso.lean`, and the two augmentations are the ones
[Stacks, Tag 03AX] already builds in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/ToSheafCohomology.lean`.

The acyclicity hypothesis is stated as the vanishing of the higher right derived functors of
`Γ(V, -) : Ab(C) ⥤ Ab` at `F`, for `V` running over the nonempty finite fibre products of the
family. That is the definition of `H^i(V, F)` used in [Stacks, Tag 03AY]; Mathlib's
`CategoryTheory.Sheaf.H'`, which is an `Ext`-group, is identified with it by
`Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf`, and that identification is not needed
here.

The generic lemmas of the first section are stated again rather than imported: their counterparts
in `Stacks.Cohomology.CechAcyclic` and `Stacks.Cohomology.CechTotalComparison` live in the
ringed-space tree, whose import closure has nothing to do with sites. Each one names its
counterpart.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open StacksDraft.TotalComplexQuasiIso

universe v u

namespace Stacks.CechSite.Acyclic

attribute [local instance] HasDerivedCategory.standard

/-! ### Generic lemmas -/

section Generic

/-- **Extension by zero is, in a degree in the range of the embedding, the original term**,
naturally in the complex. This is
`Stacks.Cohomology.CechTotalComparison.extendXIso_naturality`. -/
lemma extendXIso_naturality {B : Type*} [Category* B] [Abelian B]
    {Kc Lc : CochainComplex B ℕ} (φ : Kc ⟶ Lc) {i : ℕ} {i' : ℤ}
    (h : embeddingUpNat.f i = i') :
    (HomologicalComplex.extendMap φ embeddingUpNat).f i' ≫
        (Lc.extendXIso embeddingUpNat h).hom =
      (Kc.extendXIso embeddingUpNat h).hom ≫ φ.f i := by
  rw [HomologicalComplex.extendMap_f φ embeddingUpNat h]
  simp

/-- **A quasi-isomorphism out of a complex concentrated in degree `0` identifies its object with
the kernel of the first differential.** This is
`Stacks.Cohomology.CechTotalComparison.isIso_kernelLift_of_quasiIso_single`. -/
lemma isIso_kernelLift_of_quasiIso_single {B : Type*} [Category* B] [Abelian B] {F : B}
    {Kc : CochainComplex B ℤ} (hK : IsZero (Kc.X (-1)))
    (ψ : (HomologicalComplex.single B (up ℤ) 0).obj F ⟶ Kc) [QuasiIso ψ] (ξ : F ⟶ Kc.X 0)
    (hξ : (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫ ξ = ψ.f 0)
    (hz : ξ ≫ Kc.d 0 1 = 0) :
    IsIso (kernel.lift (Kc.d 0 1) ξ hz) := by
  have hS : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0) :=
    ((HomologicalComplex.single B (up ℤ) 0).obj F).isIso_iCycles 0 1 (by simp)
      (HomologicalComplex.single_obj_d _ _ _ _ _)
  have hSπ : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).homologyπ 0) :=
    ((HomologicalComplex.single B (up ℤ) 0).obj F).isIso_homologyπ (-1) 0 (by simp)
      (HomologicalComplex.single_obj_d _ _ _ _ _)
  have hKπ : IsIso (Kc.homologyπ 0) :=
    Kc.isIso_homologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)
  have hψ : IsIso (HomologicalComplex.homologyMap ψ 0) :=
    (quasiIsoAt_iff_isIso_homologyMap ψ 0).1 inferInstance
  have hcyc : IsIso (HomologicalComplex.cyclesMap ψ 0) := by
    have hnat := HomologicalComplex.homologyπ_naturality ψ 0
    have : IsIso (HomologicalComplex.cyclesMap ψ 0 ≫ Kc.homologyπ 0) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ (Kc.homologyπ 0)
  let hker := Kc.cyclesIsKernel 0 1 (by simp)
  let e : Kc.cycles 0 ≅ kernel (Kc.d 0 1) :=
    IsLimit.conePointUniqueUpToIso hker (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (Kc.d 0 1) = Kc.iCycles 0 :=
    IsLimit.conePointUniqueUpToIso_hom_comp hker (limit.isLimit _) WalkingParallelPair.zero
  have heq : HomologicalComplex.cyclesMap ψ 0 ≫ e.hom =
      ((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
          kernel.lift (Kc.d 0 1) ξ hz := by
    apply (cancel_mono (kernel.ι (Kc.d 0 1))).mp
    simp only [Category.assoc, he, kernel.lift_ι, HomologicalComplex.cyclesMap_i]
    rw [hξ]
  have h₁ : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0 ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
        kernel.lift (Kc.d 0 1) ξ hz) := by
    rw [← heq]; infer_instance
  have h₂ : IsIso ((HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
      kernel.lift (Kc.d 0 1) ξ hz) :=
    IsIso.of_isIso_comp_left (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0) _
  exact IsIso.of_isIso_comp_left (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom _

/-- **The inclusion of an object into the degree-zero term of an injective resolution is a kernel
of the first differential.** This is
`Stacks.Cohomology.CechTotalComparison.isIso_kernelLift_resolutionAug`, for
`CategoryTheory.InjectiveResolution.inclusionZero`. -/
lemma isIso_kernelLift_inclusionZero {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] {F : B} (J : InjectiveResolution F) :
    IsIso (kernel.lift (J.cochainComplex.d 0 1) J.inclusionZero
      (InjectiveResolution.inclusionZero_comp_d J)) :=
  isIso_kernelLift_of_quasiIso_single
    (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 (-1) (by omega)) J.ι'
    J.inclusionZero (by simp [InjectiveResolution.inclusionZero])
    (InjectiveResolution.inclusionZero_comp_d J)

/-- **The inclusion of an object into the degree-zero term of an injective resolution is a
monomorphism.** -/
lemma mono_inclusionZero {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {F : B} (J : InjectiveResolution F) : Mono J.inclusionZero := by
  have := isIso_kernelLift_inclusionZero J
  rw [← kernel.lift_ι (J.cochainComplex.d 0 1) J.inclusionZero
    (InjectiveResolution.inclusionZero_comp_d J)]
  infer_instance

/-- **The inclusion of an object into the degree-zero term of an injective resolution opens an
exact short complex.** -/
lemma exact_inclusionZero {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {F : B} (J : InjectiveResolution F) :
    (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1)
      (InjectiveResolution.inclusionZero_comp_d J)).Exact := by
  refine (ShortComplex.exact_iff_epi_kernel_lift _).2 ?_
  have := isIso_kernelLift_inclusionZero J
  infer_instance

end Generic

/-! ### The Čech cochain functor in a fixed degree is a product of sections functors -/

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{max u v} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- The fibre product `U_{k 0} ×_U ⋯ ×_U U_{k n}` selected by a tuple of members of the
family. -/
abbrev tupleObj {n : ℕ} (k : Fin (n + 1) → E.I₀) : C :=
  (∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over U).left

/-- Sections over the fibre product selected by a tuple of members of the family, as a functor of
the abelian sheaf. The Čech cochains of the family in a fixed degree are the product of these
over the tuples, and `H^q` of the covered fibre products is the `q`-th right derived functor of
this. -/
abbrev tupleSections {n : ℕ} (k : Fin (n + 1) → E.I₀) :
    Sheaf K Ab.{max u v} ⥤ Ab.{max u v} :=
  (sheafSections K Ab.{max u v}).obj (op (tupleObj E k))

/-- Sections of abelian sheaves over an object preserve finite limits: they are the composite of
the inclusion into presheaves with an evaluation, and both preserve finite limits. -/
instance preservesFiniteLimits_tupleSections {n : ℕ} (k : Fin (n + 1) → E.I₀) :
    PreservesFiniteLimits (tupleSections K E k) := by
  change PreservesFiniteLimits (sheafToPresheaf K Ab.{max u v} ⋙
    (evaluation Cᵒᵖ Ab.{max u v}).obj (op (tupleObj E k)))
  infer_instance

/-- The Čech cochains of the family in a fixed degree, as a functor of the abelian sheaf. -/
def cechTermFunctor (n : ℕ) : Sheaf K Ab.{max u v} ⥤ Ab.{max u v} :=
  sheafToPresheaf K Ab.{max u v} ⋙ cechComplexFunctor E (A := Ab.{max u v}) ⋙
    HomologicalComplex.eval Ab.{max u v} (up ℕ) n

/-- The family, indexed by the tuples of members of the covering, whose product is the Čech
cochains in degree `n`. -/
def cechEvalFamily (n : ℕ) :
    Sheaf K Ab.{max u v} ⥤ (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{max u v}) where
  obj F := Discrete.functor fun k ↦ (tupleSections K E k).obj F
  map f := Discrete.natTrans fun k ↦ (tupleSections K E k.as).map f

/-- **The Čech cochains in a fixed degree are the product of the sections over the fibre
products.** This is the degreewise description of the Čech complex of [Stacks, Tag 03AM], read as
a limit over a discrete category so that the exactness of products is available. -/
def cechTermFunctorIso (n : ℕ) :
    cechTermFunctor K E n ≅ cechEvalFamily K E n ⋙ lim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {F G} φ ↦ by
    have key : (cechTermFunctor K E n).map φ = (cechEvalFamily K E n ⋙ lim).map φ := by
      refine limit.hom_ext fun j ↦ ?_
      obtain ⟨k⟩ := j
      have h1 : (cechEvalFamily K E n ⋙ lim).map φ ≫
          limit.π ((cechEvalFamily K E n).obj G) ⟨k⟩ =
            limit.π ((cechEvalFamily K E n).obj F) ⟨k⟩ ≫
              ((sheafToPresheaf K Ab.{max u v}).map φ).app (op (tupleObj E k)) :=
        limMap_π _ _
      exact (cechComplexFunctor_map_f_π.{max u v, max u v, v, u} E
        ((sheafToPresheaf K Ab.{max u v}).map φ) n k).trans h1.symm
    exact (Category.comp_id _).trans (key.trans (Category.id_comp _).symm))

/-- The family of sections functors over the fibre products preserves finite limits: limits in a
category of functors on a discrete category are computed componentwise. -/
instance preservesFiniteLimits_cechEvalFamily (n : ℕ) :
    PreservesFiniteLimits (cechEvalFamily K E n) :=
  preservesFiniteLimits_of_evaluation _ fun ⟨k⟩ ↦ preservesFiniteLimits_tupleSections K E k

/-- **The Čech cochain functor in a fixed degree preserves finite limits**: it is a product of
sections functors, and sections of abelian sheaves over an object preserve finite limits. -/
instance preservesFiniteLimits_cechTermFunctor (n : ℕ) :
    PreservesFiniteLimits (cechTermFunctor K E n) := by
  have := preservesFiniteLimits_cechEvalFamily K E n
  exact preservesFiniteLimits_of_natIso (cechTermFunctorIso K E n).symm

/-- The Čech cochain functor in a fixed degree preserves zero morphisms, each of the three
functors it is composed of doing so. -/
instance preservesZeroMorphisms_cechTermFunctor (n : ℕ) :
    (cechTermFunctor K E n).PreservesZeroMorphisms := by
  dsimp only [cechTermFunctor]
  infer_instance

/-- In a Čech degree in the range of the embedding, the integer-graded Čech complex is the Čech
cochain functor of that degree. -/
def cechEvalIso (i : ℕ) :
    cechComplexIntFunctor.{max u v} K E ⋙ HomologicalComplex.eval Ab.{max u v} (up ℤ) (i : ℤ) ≅
      cechTermFunctor K E i :=
  NatIso.ofComponents
    (fun G ↦ cechIntXIsoPre.{max u v} E G.obj i (i : ℤ) (ComplexShape.embeddingUpNat_f i))
    (fun {_ _} f ↦ extendXIso_naturality
      ((cechComplexFunctor E).map ((sheafToPresheaf K Ab.{max u v}).map f))
      (ComplexShape.embeddingUpNat_f i))

/-! ### The rows of the Čech bicomplex of an injective resolution -/

/-- The integer-graded Čech complex of an abelian sheaf vanishes in negative degrees. -/
lemma isZero_cechComplexIntFunctor_X (F : Sheaf K Ab.{max u v}) (p : ℤ) (hp : p < 0) :
    IsZero (((cechComplexIntFunctor.{max u v} K E).obj F).X p) :=
  isZero_cechComplexIntFunctorPre_X.{max u v, max u v, v, u} E F.obj p hp

/-- A term of the Čech bicomplex vanishes as soon as its resolution-degree term does, and in
every negative Čech degree. -/
lemma isZero_cechBicomplex_X_X (J : CochainComplex (Sheaf K Ab.{max u v}) ℤ) (q p : ℤ)
    (h : IsZero (J.X q) ∨ p < 0) :
    IsZero (((cechBicomplex.{max u v} K E J).X q).X p) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval Ab.{max u v} (up ℤ) p).map_isZero
      ((cechComplexIntFunctor.{max u v} K E).map_isZero h)
  · exact isZero_cechComplexIntFunctorPre_X.{max u v, max u v, v, u} E (J.X q).obj p h

section Acyclic

variable [HasSheafify K Ab.{max u v}] [EnoughInjectives (Sheaf K Ab.{max u v})]
  {F : Sheaf K Ab.{max u v}} (J : InjectiveResolution F)

/-- **The Čech cochains of an injective resolution in a fixed Čech degree form a complex exact
away from resolution degree zero.** Each factor is exact away from degree zero by acyclicity on
the corresponding fibre product, exactness over a discrete index is exactness in each component,
and products are exact in `AddCommGrpCat`. -/
lemma exactAt_cechTerm_cochainComplex (n : ℕ)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F))
    (q : ℤ) (hq : q ≠ 0) :
    (((cechTermFunctor K E n).mapHomologicalComplex (up ℤ)).obj
      J.cochainComplex).ExactAt q := by
  have hfactor : ∀ k : Fin (n + 1) → E.I₀,
      ((J.cochainComplex.sc q).map (tupleSections K E k)).Exact := by
    intro k
    have hx := InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex
      (tupleSections K E k) J (fun m hm ↦ hac n k m hm) q hq
    rwa [HomologicalComplex.exactAt_iff] at hx
  have hfam : ((J.cochainComplex.sc q).map (cechEvalFamily K E n)).Exact := by
    refine ShortComplex.exact_of_app_discrete _ fun j ↦ ?_
    obtain ⟨k⟩ := j
    exact hfactor k
  have hlim : (((J.cochainComplex.sc q).map (cechEvalFamily K E n)).map
      (lim : (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{max u v}) ⥤
        Ab.{max u v})).Exact := hfam.map lim
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso (J.cochainComplex.sc q) (cechTermFunctorIso K E n)).symm hlim

/-- **The rows of the Čech bicomplex of an injective resolution are exact away from resolution
degree zero.** In negative Čech degrees the row vanishes; elsewhere the row is the Čech cochains
of the resolution in a fixed degree. -/
lemma exactAt_cechBicomplexFlip_X
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F))
    (p q : ℤ) (hq : q ≠ 0) :
    (((cechBicomplex.{max u v} K E J.cochainComplex).flip).X p).ExactAt q := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechBicomplex_X_X K E J.cochainComplex q p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hiso : ((cechBicomplex.{max u v} K E J.cochainComplex).flip).X (i : ℤ) ≅
        ((cechTermFunctor K E i).mapHomologicalComplex (up ℤ)).obj J.cochainComplex :=
      (NatIso.mapHomologicalComplex (cechEvalIso K E i) (up ℤ)).app J.cochainComplex
    exact (exactAt_cechTerm_cochainComplex K E J i hac q hq).of_iso hiso.symm

omit [EnoughInjectives (Sheaf K Ab.{max u v})] in
/-- **The kernel clause of [Stacks, Tag 0133] for the rows of the Čech bicomplex**: the Čech
complex of the resolved sheaf is, in each Čech degree, a kernel of the first differential of the
row. In negative Čech degrees both terms vanish; elsewhere this is the image of the corresponding
clause for the resolution under the Čech cochain functor, which preserves finite limits. -/
lemma inducesIsoKernel_cechBetaRow (p : ℤ) :
    ∃ hβ : ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p ≫
        (((cechBicomplex.{max u v} K E J.cochainComplex).flip).X p).d 0 1 = 0,
      IsIso (kernel.lift ((((cechBicomplex.{max u v} K E J.cochainComplex).flip).X p).d 0 1)
        (((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p) hβ) := by
  have hz := InjectiveResolution.inclusionZero_comp_d J
  have hβ : ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p ≫
      (((cechBicomplex.{max u v} K E J.cochainComplex).flip).X p).d 0 1 = 0 := by
    show ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p ≫
      ((cechComplexIntFunctor.{max u v} K E).map (J.cochainComplex.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
      HomologicalComplex.zero_f]
  refine ⟨hβ, ?_⟩
  have hmonoξ : Mono J.inclusionZero := mono_inclusionZero J
  rcases lt_or_ge p 0 with hp | hp
  · refine isIso_of_isZero _ (isZero_cechComplexIntFunctor_X K E F p hp) ?_
    exact IsZero.of_mono (kernel.ι _)
      (isZero_cechBicomplex_X_X K E J.cochainComplex 0 p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hS : (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1) hz).Exact :=
      exact_inclusionZero J
    have hexT := hS.map_of_mono_of_preservesKernel (cechTermFunctor K E i) hmonoξ
      inferInstance
    have eiso : (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1) hz).map
          (cechTermFunctor K E i) ≅
        ShortComplex.mk (((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f (i : ℤ))
          ((((cechBicomplex.{max u v} K E J.cochainComplex).flip).X (i : ℤ)).d 0 1) hβ :=
      ShortComplex.isoMk ((cechEvalIso K E i).app F).symm
        ((cechEvalIso K E i).app (J.cochainComplex.X 0)).symm
        ((cechEvalIso K E i).app (J.cochainComplex.X 1)).symm
        ((cechEvalIso K E i).inv.naturality J.inclusionZero).symm
        ((cechEvalIso K E i).inv.naturality (J.cochainComplex.d 0 1)).symm
    obtain ⟨hex, hmono⟩ := (ShortComplex.exact_and_mono_f_iff_of_iso eiso).1
      ⟨hexT, (inferInstance : Mono ((cechTermFunctor K E i).map J.inclusionZero))⟩
    exact @Stacks.Cohomology.CechTotalComparison.isIso_kernelLift_of_mono_of_exact
      _ _ _ _ _ _ _ _ _ hmono hex

/-- **The augmentation `β`**, as a morphism into the zeroth row of the flipped Čech bicomplex: in
Čech degree `p` it is the Čech `p`-cochains of the inclusion `F ⟶ J^0`. -/
def cechBetaRow :
    (cechComplexIntFunctor.{max u v} K E).obj F ⟶
      rowZero ((cechBicomplex.{max u v} K E J.cochainComplex).flip) where
  f p := ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p
  comm' p p' _ := ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).comm p p'

omit [EnoughInjectives (Sheaf K Ab.{max u v})] in
/-- The components of `Stacks.CechSite.Acyclic.cechBetaRow`. -/
@[simp]
lemma cechBetaRow_f (p : ℤ) :
    (cechBetaRow K E J).f p =
      ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p := rfl

omit [EnoughInjectives (Sheaf K Ab.{max u v})] in
/-- **The antidiagonals of the flipped Čech bicomplex are finite.** -/
lemma diagonalFinite_cechBicomplexFlip :
    DiagonalFinite ((cechBicomplex.{max u v} K E J.cochainComplex).flip) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X K E J.cochainComplex (n - p) p
      (Or.inr (by omega)))
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X K E J.cochainComplex (n - p) p
      (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 (n - p) (by omega))))

/-- **The hypotheses of [Stacks, Tag 0133] for the flipped Čech bicomplex of an injective
resolution of an acyclic sheaf**, with the augmentation by the Čech complex of the resolved
sheaf. -/
theorem hypotheses_cechBetaRow
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F)) :
    Hypotheses ((cechComplexIntFunctor.{max u v} K E).obj F)
      ((cechBicomplex.{max u v} K E J.cochainComplex).flip) (cechBetaRow K E J) where
  diagonalFinite := diagonalFinite_cechBicomplexFlip K E J
  zero_of_neg p q hq := isZero_cechBicomplex_X_X K E J.cochainComplex q p
    (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := exactAt_cechBicomplexFlip_X K E J hac p q hq
  inducesIsoKernel p := inducesIsoKernel_cechBetaRow K E J p

/-! ### The comparison is an isomorphism -/

/-- The components of the comparison map of [Stacks, Tag 0133] for the rows, read in the total
complex of the Čech bicomplex. The sign that flipping a total complex introduces is
`(-1)^{0 · p}`, hence trivial. -/
lemma comparisonMapP_totalFlipIso_f
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F))
    (p : ℤ) :
    (comparisonMapP ((cechComplexIntFunctor.{max u v} K E).obj F)
          ((cechBicomplex.{max u v} K E J.cochainComplex).flip) (cechBetaRow K E J)
          (hypotheses_cechBetaRow K E J hac) ≫
        ((cechBicomplex.{max u v} K E J.cochainComplex).totalFlipIso (up ℤ)).hom).f p =
      ((cechComplexIntFunctor.{max u v} K E).map J.inclusionZero).f p ≫
        (cechBicomplex.{max u v} K E J.cochainComplex).ιTotal (up ℤ) 0 p p (by simp) := by
  rw [HomologicalComplex.comp_f, comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp only [rowZero_X, cechBetaRow_f, σ_def, zero_mul, Int.negOnePow_zero, one_smul]
  rfl

/-- **The augmentation `β` of [Stacks, Tag 03AX] is the comparison map of [Stacks, Tag 0133] for
the rows.** Both are given in Čech degree `p` by the `p`-cochains of `F ⟶ J^0`, landing in the
`(0, p)` corner of the total complex. -/
lemma cechToTotal_eq
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F)) :
    cechToTotal.{max u v} K E F J =
      comparisonMapP ((cechComplexIntFunctor.{max u v} K E).obj F)
          ((cechBicomplex.{max u v} K E J.cochainComplex).flip) (cechBetaRow K E J)
          (hypotheses_cechBetaRow K E J hac) ≫
        ((cechBicomplex.{max u v} K E J.cochainComplex).totalFlipIso (up ℤ)).hom :=
  HomologicalComplex.hom_ext _ _ fun p ↦
    (comparisonMapP_totalFlipIso_f K E J hac p).symm

/-- **The augmentation `β` is a quasi-isomorphism** for an acyclic covering family, by
[Stacks, Tag 0133]: the rows of the Čech bicomplex of the resolution are exact away from
resolution degree zero and the Čech complex of `F` is their kernel in degree zero. -/
lemma quasiIso_cechToTotal
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F)) :
    QuasiIso (cechToTotal.{max u v} K E F J) := by
  have hq := quasiIso_comparisonMapP ((cechComplexIntFunctor.{max u v} K E).obj F)
    ((cechBicomplex.{max u v} K E J.cochainComplex).flip) (cechBetaRow K E J)
    (hypotheses_cechBetaRow K E J hac)
  rw [cechToTotal_eq K E J hac]
  infer_instance

/-- **The comparison at an injective resolution is an isomorphism** for an acyclic covering
family. Of its three factors `Q(β)`, `Q(α)⁻¹` and the identification of the sections of the
resolution with derived sections, the last two are isomorphisms for every covering family, and
the first is one here because `β` is a quasi-isomorphism. -/
lemma isIso_cechComparison (hE : Sieve.generate E.presieve₀ ∈ K U)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F)) :
    IsIso (cechComparison.{max u v} K E hE F J) := by
  have hβ := quasiIso_cechToTotal K E J hac
  have hQβ : IsIso (DerivedCategory.Q.map (cechToTotal.{max u v} K E F J)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hβ
  dsimp only [cechComparison]
  infer_instance

end Acyclic

section Statement

variable [HasSheafify K Ab.{max u v}] [EnoughInjectives (Sheaf K Ab.{max u v})]
  (hE : Sieve.generate E.presieve₀ ∈ K U)

/-- **The Čech-to-derived-sections transformation of [Stacks, Tag 03AX] is an isomorphism at an
abelian sheaf which is acyclic on the fibre products of the covering family.** -/
lemma isIso_cechToDerivedSections_app (F : Sheaf K Ab.{max u v})
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections K E s).rightDerived m).obj F)) :
    IsIso ((cechToDerivedSections.{max u v} K E hE).app F) := by
  refine (ObjectProperty.isIso_hom_iff _).1 ?_
  exact isIso_cechComparison K E (InjectiveResolution.of F) hE hac

/-- **Stacks Project, Tag 03F7.** Let `𝒰 = {U_i → U}` be a covering family of an object of a
site and let `F` be an abelian sheaf whose higher cohomology vanishes on every nonempty finite
fibre product `U_{i_0} ×_U ⋯ ×_U U_{i_r}` of members of the family. Then the canonical
comparison of [Stacks, Tag 03AX]

```
Ȟ^p(𝒰, F) ⟶ H^p(U, F)
```

is an isomorphism in every degree `p`: the Čech cohomology of such a family computes the sheaf
cohomology of the covered object. -/
@[stacks 03F7]
theorem isIso_cechCohomologyToCohomology_app (F : Sheaf K Ab.{max u v})
    (hacyclic : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (q : ℕ), 0 < q →
      IsZero (((tupleSections K E s).rightDerived q).obj F))
    (p : ℤ) :
    IsIso ((cechCohomologyToCohomology.{max u v} K E hE p).app F) := by
  have hτ : IsIso ((cechToDerivedSections.{max u v} K E hE).app F) :=
    isIso_cechToDerivedSections_app K E hE F hacyclic
  dsimp only [cechCohomologyToCohomology]
  rw [Functor.whiskerRight_app]
  infer_instance

end Statement

end Stacks.CechSite.Acyclic

end

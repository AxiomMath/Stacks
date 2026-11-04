module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Algebra.Homology.ShortComplex.DiscreteFunctorCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Čech cohomology of an acyclic covering family on a site, in arbitrary universes

Let `C` be a site, let `𝒰 = {U_i → U}` be a covering family of an object `U` and let `F` be an
abelian sheaf on `C` whose higher cohomology vanishes on every nonempty finite fibre product
`U_{i_0} ×_U ⋯ ×_U U_{i_p}` of members of the family. Then the canonical comparison
`Stacks.CechSite.cechCohomologyToCohomology` of [Stacks, Tag 03AX], from the Čech cohomology of
the family to the cohomology of `F` over `U`, is an isomorphism in every degree. This is
[Stacks, Tag 03F7].

`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/AcyclicCoveringFamily.lean` proves this for a
covering family indexed in the universe `max u v` of a site `C : Type u` with `Category.{v} C`,
with coefficients in `Ab.{max u v}`. This file proves it with the covering family indexed in an
arbitrary universe `w` and the coefficients in `Ab.{max a u v w}` for an arbitrary universe `a`,
which is what a small family of a large site needs (a finite affine covering of an object of the
pro-étale site, say, whose coefficients live one universe up). The argument is the same; the only
new input is that products indexed by the tuples of members of the family, a type of universe `w`,
are exact in `Ab.{max a u v w}`, which is Mathlib's `CategoryTheory.AB4StarOfSize_shrink`. The
generic lemmas on injective resolutions and extension by zero are those of
`Stacks.CechSite.Acyclic`.

## Main results

* `Stacks.CechSite.AcyclicOfSize.isIso_cechCohomologyToCohomology_app`: [Stacks, Tag 03F7] in
  arbitrary universes — the comparison `Ȟ^p(𝒰, F) ⟶ H^p(U, F)` is an isomorphism.
* `Stacks.CechSite.AcyclicOfSize.isIso_cechToDerivedSections_app`: the same before passing to
  cohomology — the Čech complex of `F` *is* `RΓ(U, F)` in the derived category.
* `Stacks.CechSite.AcyclicOfSize.isZero_rightDerived_of_isZero_cechCohomology`: for such a family,
  `H^p(U, F)` vanishes as soon as `Ȟ^p(𝒰, F)` does.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open StacksDraft.TotalComplexQuasiIso

universe a w v u

namespace Stacks.CechSite.AcyclicOfSize

attribute [local instance] HasDerivedCategory.standard

/-! ### The Čech cochain functor in a fixed degree is a product of sections functors -/

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- Sections over the fibre product `U_{k 0} ×_U ⋯ ×_U U_{k n}` selected by a tuple of members
of the family, as a functor of the abelian sheaf. The Čech cochains of the family in a fixed degree
are the product of these over the tuples, and `H^q` of the covered fibre products is the `q`-th
right derived functor of this. -/
abbrev tupleSections {n : ℕ} (k : Fin (n + 1) → E.I₀) :
    Sheaf K Ab.{max a u v w} ⥤ Ab.{max a u v w} :=
  (sheafSections K Ab.{max a u v w}).obj (op (∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over U).left)

/-- Sections of abelian sheaves over an object preserve finite limits: they are the composite of
the inclusion into presheaves with an evaluation, and both preserve finite limits. -/
instance preservesFiniteLimits_tupleSections {n : ℕ} (k : Fin (n + 1) → E.I₀) :
    PreservesFiniteLimits (tupleSections.{a} K E k) := by
  change PreservesFiniteLimits (sheafToPresheaf K Ab.{max a u v w} ⋙
    (evaluation Cᵒᵖ Ab.{max a u v w}).obj (op (∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over U).left))
  infer_instance

/-- The Čech cochains of the family in a fixed degree, as a functor of the abelian sheaf. -/
def cechTermFunctor (n : ℕ) : Sheaf K Ab.{max a u v w} ⥤ Ab.{max a u v w} :=
  sheafToPresheaf K Ab.{max a u v w} ⋙ cechComplexFunctor E (A := Ab.{max a u v w}) ⋙
    HomologicalComplex.eval Ab.{max a u v w} (up ℕ) n

/-- The family, indexed by the tuples of members of the covering, whose product is the Čech
cochains in degree `n`. -/
def cechEvalFamily (n : ℕ) :
    Sheaf K Ab.{max a u v w} ⥤ (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{max a u v w}) where
  obj F := Discrete.functor fun k ↦ (tupleSections.{a} K E k).obj F
  map f := Discrete.natTrans fun k ↦ (tupleSections.{a} K E k.as).map f

/-- **The Čech cochains in a fixed degree are the product of the sections over the fibre
products.** This is the degreewise description of the Čech complex of [Stacks, Tag 03AM], read as
a limit over a discrete category so that the exactness of products is available. -/
def cechTermFunctorIso (n : ℕ) :
    cechTermFunctor.{a} K E n ≅ cechEvalFamily.{a} K E n ⋙ lim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {F G} φ ↦ by
    have key : (cechTermFunctor.{a} K E n).map φ = (cechEvalFamily.{a} K E n ⋙ lim).map φ := by
      refine limit.hom_ext fun ⟨k⟩ ↦ ?_
      have h1 : (cechEvalFamily.{a} K E n ⋙ lim).map φ ≫
          limit.π ((cechEvalFamily.{a} K E n).obj G) ⟨k⟩ =
            limit.π ((cechEvalFamily.{a} K E n).obj F) ⟨k⟩ ≫
              _ :=
        limMap_π _ _
      exact (cechComplexFunctor_map_f_π.{max a u v w, w, v, u} E
        ((sheafToPresheaf K Ab.{max a u v w}).map φ) n k).trans h1.symm
    exact (Category.comp_id _).trans (key.trans (Category.id_comp _).symm))

/-- The family of sections functors over the fibre products preserves finite limits: limits in a
category of functors on a discrete category are computed componentwise. -/
instance preservesFiniteLimits_cechEvalFamily (n : ℕ) :
    PreservesFiniteLimits (cechEvalFamily.{a} K E n) :=
  preservesFiniteLimits_of_evaluation _ fun ⟨k⟩ ↦ preservesFiniteLimits_tupleSections.{a} K E k

/-- **The Čech cochain functor in a fixed degree preserves finite limits**: it is a product of
sections functors, and sections of abelian sheaves over an object preserve finite limits. -/
instance preservesFiniteLimits_cechTermFunctor (n : ℕ) :
    PreservesFiniteLimits (cechTermFunctor.{a} K E n) :=
  preservesFiniteLimits_of_natIso (cechTermFunctorIso.{a} K E n).symm

/-- The Čech cochain functor in a fixed degree preserves zero morphisms, each of the three
functors it is composed of doing so. -/
instance preservesZeroMorphisms_cechTermFunctor (n : ℕ) :
    (cechTermFunctor.{a} K E n).PreservesZeroMorphisms := by
  dsimp only [cechTermFunctor]
  infer_instance

/-- In a Čech degree in the range of the embedding, the integer-graded Čech complex is the Čech
cochain functor of that degree. -/
def cechEvalIso (i : ℕ) :
    cechComplexIntFunctor.{a} K E ⋙ HomologicalComplex.eval Ab.{max a u v w} (up ℤ) (i : ℤ) ≅
      cechTermFunctor.{a} K E i :=
  NatIso.ofComponents
    (fun G ↦ cechIntXIsoPre.{a} E G.obj i (i : ℤ) (ComplexShape.embeddingUpNat_f i))
    (fun {_ _} f ↦ Acyclic.extendXIso_naturality
      ((cechComplexFunctor E).map ((sheafToPresheaf K Ab.{max a u v w}).map f))
      (ComplexShape.embeddingUpNat_f i))

/-! ### The rows of the Čech bicomplex of an injective resolution -/

/-- The integer-graded Čech complex of an abelian sheaf vanishes in negative degrees. -/
lemma isZero_cechComplexIntFunctor_X (F : Sheaf K Ab.{max a u v w}) (p : ℤ) (hp : p < 0) :
    IsZero (((cechComplexIntFunctor.{a} K E).obj F).X p) :=
  isZero_cechComplexIntFunctorPre_X.{a, w, v, u} E F.obj p hp

/-- A term of the Čech bicomplex vanishes as soon as its resolution-degree term does, and in
every negative Čech degree. -/
lemma isZero_cechBicomplex_X_X (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ) (q p : ℤ)
    (h : IsZero (J.X q) ∨ p < 0) :
    IsZero (((cechBicomplex.{a} K E J).X q).X p) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval Ab.{max a u v w} (up ℤ) p).map_isZero
      ((cechComplexIntFunctor.{a} K E).map_isZero h)
  · exact isZero_cechComplexIntFunctorPre_X.{a, w, v, u} E (J.X q).obj p h

section Acyclic

variable [HasSheafify K Ab.{max a u v w}] [EnoughInjectives (Sheaf K Ab.{max a u v w})]
  {F : Sheaf K Ab.{max a u v w}} (J : InjectiveResolution F)

/-- **The Čech cochains of an injective resolution in a fixed Čech degree form a complex exact
away from resolution degree zero.** Each factor is exact away from degree zero by acyclicity on
the corresponding fibre product, exactness over a discrete index is exactness in each component,
and products are exact in `AddCommGrpCat`. -/
lemma exactAt_cechTerm_cochainComplex (n : ℕ)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F))
    (q : ℤ) (hq : q ≠ 0) :
    (((cechTermFunctor.{a} K E n).mapHomologicalComplex (up ℤ)).obj
      J.cochainComplex).ExactAt q := by
  have hfam : ((J.cochainComplex.sc q).map (cechEvalFamily.{a} K E n)).Exact := by
    refine ShortComplex.exact_of_app_discrete _ fun ⟨k⟩ ↦ ?_
    have hx := InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex
      (tupleSections.{a} K E k) J (fun m hm ↦ hac n k m hm) q hq
    rwa [HomologicalComplex.exactAt_iff] at hx
  -- products indexed by the tuples, of the covering-index universe, are exact
  have : AB4StarOfSize.{w} Ab.{max a u v w} := AB4StarOfSize_shrink.{w, max a u v} _
  have hlim : (((J.cochainComplex.sc q).map (cechEvalFamily.{a} K E n)).map
      (lim : (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{max a u v w}) ⥤
        Ab.{max a u v w})).Exact := hfam.map lim
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso (J.cochainComplex.sc q) (cechTermFunctorIso.{a} K E n)).symm hlim

/-- **The rows of the Čech bicomplex of an injective resolution are exact away from resolution
degree zero.** In negative Čech degrees the row vanishes; elsewhere the row is the Čech cochains
of the resolution in a fixed degree. -/
lemma exactAt_cechBicomplexFlip_X
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F))
    (p q : ℤ) (hq : q ≠ 0) :
    (((cechBicomplex.{a} K E J.cochainComplex).flip).X p).ExactAt q := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechBicomplex_X_X.{a} K E J.cochainComplex q p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hiso : ((cechBicomplex.{a} K E J.cochainComplex).flip).X (i : ℤ) ≅
        ((cechTermFunctor.{a} K E i).mapHomologicalComplex (up ℤ)).obj J.cochainComplex :=
      (NatIso.mapHomologicalComplex (cechEvalIso.{a} K E i) (up ℤ)).app J.cochainComplex
    exact (exactAt_cechTerm_cochainComplex.{a} K E J i hac q hq).of_iso hiso.symm

omit [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- **The kernel clause of [Stacks, Tag 0133] for the rows of the Čech bicomplex**: the Čech
complex of the resolved sheaf is, in each Čech degree, a kernel of the first differential of the
row. In negative Čech degrees both terms vanish; elsewhere this is the image of the corresponding
clause for the resolution under the Čech cochain functor, which preserves finite limits. -/
lemma inducesIsoKernel_cechBetaRow (p : ℤ) :
    ∃ hβ : ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
        (((cechBicomplex.{a} K E J.cochainComplex).flip).X p).d 0 1 = 0,
      IsIso (kernel.lift ((((cechBicomplex.{a} K E J.cochainComplex).flip).X p).d 0 1)
        (((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p) hβ) := by
  have hz := InjectiveResolution.inclusionZero_comp_d J
  have hβ : ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
      (((cechBicomplex.{a} K E J.cochainComplex).flip).X p).d 0 1 = 0 := by
    show ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
      ((cechComplexIntFunctor.{a} K E).map (J.cochainComplex.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
      HomologicalComplex.zero_f]
  refine ⟨hβ, ?_⟩
  have hmonoξ : Mono J.inclusionZero := Acyclic.mono_inclusionZero J
  rcases lt_or_ge p 0 with hp | hp
  · refine isIso_of_isZero _ (isZero_cechComplexIntFunctor_X.{a} K E F p hp) ?_
    exact IsZero.of_mono (kernel.ι _)
      (isZero_cechBicomplex_X_X.{a} K E J.cochainComplex 0 p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hS : (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1) hz).Exact :=
      Acyclic.exact_inclusionZero J
    have hexT := hS.map_of_mono_of_preservesKernel (cechTermFunctor.{a} K E i) hmonoξ
      inferInstance
    have eiso : (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1) hz).map
          (cechTermFunctor.{a} K E i) ≅
        ShortComplex.mk (((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f (i : ℤ))
          ((((cechBicomplex.{a} K E J.cochainComplex).flip).X (i : ℤ)).d 0 1) hβ :=
      ShortComplex.isoMk ((cechEvalIso.{a} K E i).app F).symm
        ((cechEvalIso.{a} K E i).app (J.cochainComplex.X 0)).symm
        ((cechEvalIso.{a} K E i).app (J.cochainComplex.X 1)).symm
        ((cechEvalIso.{a} K E i).inv.naturality J.inclusionZero).symm
        ((cechEvalIso.{a} K E i).inv.naturality (J.cochainComplex.d 0 1)).symm
    obtain ⟨hex, hmono⟩ :=
      (ShortComplex.exact_and_mono_f_iff_of_iso eiso).1 ⟨hexT, by dsimp; infer_instance⟩
    exact @Stacks.Cohomology.CechTotalComparison.isIso_kernelLift_of_mono_of_exact
      _ _ _ _ _ _ _ _ _ hmono hex

/-- **The augmentation `β`**, as a morphism into the zeroth row of the flipped Čech bicomplex: in
Čech degree `p` it is the Čech `p`-cochains of the inclusion `F ⟶ J^0`. -/
def cechBetaRow :
    (cechComplexIntFunctor.{a} K E).obj F ⟶
      rowZero ((cechBicomplex.{a} K E J.cochainComplex).flip) where
  f p := ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p
  comm' p p' _ := ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).comm p p'

omit [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- The components of `Stacks.CechSite.AcyclicOfSize.cechBetaRow`. -/
@[simp]
lemma cechBetaRow_f (p : ℤ) :
    (cechBetaRow.{a} K E J).f p =
      ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p := rfl

omit [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- **The antidiagonals of the flipped Čech bicomplex are finite.** -/
lemma diagonalFinite_cechBicomplexFlip :
    DiagonalFinite ((cechBicomplex.{a} K E J.cochainComplex).flip) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X.{a} K E J.cochainComplex (n - p) p
      (Or.inr (by omega)))
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X.{a} K E J.cochainComplex (n - p) p
      (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 (n - p) (by omega))))

/-- **The hypotheses of [Stacks, Tag 0133] for the flipped Čech bicomplex of an injective
resolution of an acyclic sheaf**, with the augmentation by the Čech complex of the resolved
sheaf. -/
theorem hypotheses_cechBetaRow
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F)) :
    Hypotheses ((cechComplexIntFunctor.{a} K E).obj F)
      ((cechBicomplex.{a} K E J.cochainComplex).flip) (cechBetaRow.{a} K E J) where
  diagonalFinite := diagonalFinite_cechBicomplexFlip.{a} K E J
  zero_of_neg p q hq := isZero_cechBicomplex_X_X.{a} K E J.cochainComplex q p
    (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := exactAt_cechBicomplexFlip_X.{a} K E J hac p q hq
  inducesIsoKernel p := inducesIsoKernel_cechBetaRow.{a} K E J p

/-! ### The comparison is an isomorphism -/

/-- The components of the comparison map of [Stacks, Tag 0133] for the rows, read in the total
complex of the Čech bicomplex. The sign that flipping a total complex introduces is
`(-1)^{0 · p}`, hence trivial. -/
lemma comparisonMapP_totalFlipIso_f
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F))
    (p : ℤ) :
    (comparisonMapP ((cechComplexIntFunctor.{a} K E).obj F)
          ((cechBicomplex.{a} K E J.cochainComplex).flip) (cechBetaRow.{a} K E J)
          (hypotheses_cechBetaRow.{a} K E J hac) ≫
        ((cechBicomplex.{a} K E J.cochainComplex).totalFlipIso (up ℤ)).hom).f p =
      ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
        (cechBicomplex.{a} K E J.cochainComplex).ιTotal (up ℤ) 0 p p (by simp) := by
  rw [HomologicalComplex.comp_f, comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp only [rowZero_X, cechBetaRow_f, σ_def, zero_mul, Int.negOnePow_zero, one_smul]
  rfl

/-- **The augmentation `β` of [Stacks, Tag 03AX] is the comparison map of [Stacks, Tag 0133] for
the rows.** Both are given in Čech degree `p` by the `p`-cochains of `F ⟶ J^0`, landing in the
`(0, p)` corner of the total complex. -/
lemma cechToTotal_eq
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F)) :
    cechToTotal.{a} K E F J =
      comparisonMapP ((cechComplexIntFunctor.{a} K E).obj F)
          ((cechBicomplex.{a} K E J.cochainComplex).flip) (cechBetaRow.{a} K E J)
          (hypotheses_cechBetaRow.{a} K E J hac) ≫
        ((cechBicomplex.{a} K E J.cochainComplex).totalFlipIso (up ℤ)).hom :=
  HomologicalComplex.hom_ext _ _ fun p ↦
    (comparisonMapP_totalFlipIso_f.{a} K E J hac p).symm

/-- **The augmentation `β` is a quasi-isomorphism** for an acyclic covering family, by
[Stacks, Tag 0133]: the rows of the Čech bicomplex of the resolution are exact away from
resolution degree zero and the Čech complex of `F` is their kernel in degree zero. -/
lemma quasiIso_cechToTotal
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F)) :
    QuasiIso (cechToTotal.{a} K E F J) := by
  have hq := quasiIso_comparisonMapP ((cechComplexIntFunctor.{a} K E).obj F)
    ((cechBicomplex.{a} K E J.cochainComplex).flip) (cechBetaRow.{a} K E J)
    (hypotheses_cechBetaRow.{a} K E J hac)
  rw [cechToTotal_eq.{a} K E J hac]
  infer_instance

/-- **The comparison at an injective resolution is an isomorphism** for an acyclic covering
family. Of its three factors `Q(β)`, `Q(α)⁻¹` and the identification of the sections of the
resolution with derived sections, the last two are isomorphisms for every covering family, and
the first is one here because `β` is a quasi-isomorphism. -/
lemma isIso_cechComparison (hE : Sieve.generate E.presieve₀ ∈ K U)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F)) :
    IsIso (cechComparison.{a} K E hE F J) := by
  have hQβ : IsIso (DerivedCategory.Q.map (cechToTotal.{a} K E F J)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_cechToTotal.{a} K E J hac)
  dsimp only [cechComparison]
  infer_instance

end Acyclic

section Statement

variable [HasSheafify K Ab.{max a u v w}] [EnoughInjectives (Sheaf K Ab.{max a u v w})]
  (hE : Sieve.generate E.presieve₀ ∈ K U)

/-- **The Čech-to-derived-sections transformation of [Stacks, Tag 03AX] is an isomorphism at an
abelian sheaf which is acyclic on the fibre products of the covering family.** -/
lemma isIso_cechToDerivedSections_app (F : Sheaf K Ab.{max a u v w})
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (m : ℕ), 0 < m →
      IsZero (((tupleSections.{a} K E s).rightDerived m).obj F)) :
    IsIso ((cechToDerivedSections.{a} K E hE).app F) :=
  (ObjectProperty.isIso_hom_iff _).1
    (isIso_cechComparison.{a} K E (InjectiveResolution.of F) hE hac)

/-- **Stacks Project, Tag 03F7.** Let `𝒰 = {U_i → U}` be a covering family of an object of a
site and let `F` be an abelian sheaf whose higher cohomology vanishes on every nonempty finite
fibre product `U_{i_0} ×_U ⋯ ×_U U_{i_r}` of members of the family. Then the canonical
comparison of [Stacks, Tag 03AX]

```
Ȟ^p(𝒰, F) ⟶ H^p(U, F)
```

is an isomorphism in every degree `p`: the Čech cohomology of such a family computes the sheaf
cohomology of the covered object. -/
theorem isIso_cechCohomologyToCohomology_app (F : Sheaf K Ab.{max a u v w})
    (hacyclic : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (q : ℕ), 0 < q →
      IsZero (((tupleSections.{a} K E s).rightDerived q).obj F))
    (p : ℤ) :
    IsIso ((cechCohomologyToCohomology.{a} K E hE p).app F) := by
  have hτ : IsIso ((cechToDerivedSections.{a} K E hE).app F) :=
    isIso_cechToDerivedSections_app.{a} K E hE F hacyclic
  dsimp only [cechCohomologyToCohomology]
  rw [Functor.whiskerRight_app]
  infer_instance

include hE in
/-- **Vanishing of cohomology over an object from Čech cohomology.** Let `𝒰 = {U_i → U}` be a
covering family and let `F` be an abelian sheaf whose higher cohomology vanishes on every finite
fibre product of members of `𝒰`. If the Čech cohomology `Ȟ^p(𝒰, F)` vanishes, so does the
cohomology `H^p(U, F)`, the `p`-th right derived functor of `Γ(U, -)` at `F`: the two are
isomorphic by [Stacks, Tag 03F7]. -/
theorem isZero_rightDerived_of_isZero_cechCohomology (F : Sheaf K Ab.{max a u v w})
    (hacyclic : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (q : ℕ), 0 < q →
      IsZero (((tupleSections.{a} K E s).rightDerived q).obj F))
    (p : ℕ) (hp : IsZero (cechCohomology E F.obj p)) :
    IsZero ((((sheafSections K Ab.{max a u v w}).obj (op U)).rightDerived p).obj F) := by
  have := isIso_cechCohomologyToCohomology_app K E hE F hacyclic p
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso _ p).app F)
  refine IsZero.of_iso ?_ (asIso ((cechCohomologyToCohomology.{a} K E hE p).app F)).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ (p : ℤ)).app
    (((cechComplexFunctor E).obj F.obj).extend ComplexShape.embeddingUpNat))
  exact hp.of_iso (HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingUpNat_f p))

end Statement

end Stacks.CechSite.AcyclicOfSize

end

module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialPolynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of quotients of `𝒪^{⊕ r}` on `ℙⁿ_T`

For a morphism `g : T' ⟶ T` the pullback `AlgebraicGeometry.ProjectiveQuot.baseChange g K` of a
submodule `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T` has quotient the pullback of the quotient of `K`, and the
conditions defining `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` and `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` are stable under
it. This is what makes `T ↦ Quot^P(T)` a functor (Stacks 09TR, 0DNF), the object whose
properness is Stacks 0DPA.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.quotientBaseChangeIso`: the quotient of the base change is
  the pullback of the quotient (right exactness of the inverse image).

## Main results

* `AlgebraicGeometry.hilbertPolynomial_eq_of_iso`: isomorphic coherent sheaves on `ℙⁿ_k` have
  the same Hilbert polynomial.
* `AlgebraicGeometry.ProjectiveQuot.baseChange_mem_families`: finite presentation and flatness
  over the base are stable under base change (Stacks 01BQ, 01U8).
* `AlgebraicGeometry.ProjectiveQuot.baseChange_mem_hilbertFamilies`: so is the fibre Hilbert
  polynomial, since the fibre of the base change at `t'` is the extension of scalars of the fibre
  at `g t'` along `κ(g t') ⟶ κ(t')`, and the Hilbert polynomial does not change under extension of
  the ground field.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The Hilbert polynomial is an isomorphism invariant.** -/
theorem hilbertPolynomial_eq_of_iso (k : Type u) [Field k] (n : ℕ)
    {F G : (projectiveSpaceOverRing n (.of k)).Modules} [F.IsCoherent] [G.IsCoherent]
    (e : F ≅ G) (d : ℤ) :
    hilbertPolynomial k n F d = hilbertPolynomial k n G d := by
  unfold hilbertPolynomial
  refine finsum_congr fun i => ?_
  have e' : projectiveTwist n F d ≅ projectiveTwist n G d :=
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n d).mapIso e
  rw [finrank_cohomologyOverField_eq_of_iso k
    (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) e' i]

namespace ProjectiveQuot

variable {n r : ℕ}

/-- The pulled-back quotient map is a cokernel of the inclusion of its kernel: in an abelian
category an epimorphism is the cokernel of its kernel. -/
def baseChangeIsColimit {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    IsColimit (CokernelCofork.ofπ (baseChangeQuotientMap g K)
      (kernelSubobject_arrow_comp (baseChangeQuotientMap g K))) :=
  Abelian.epiIsCokernelOfKernel _
    (IsLimit.ofIsoLimit (kernelIsKernel (baseChangeQuotientMap g K))
      (Fork.ext (t := KernelFork.ofι _ (kernelSubobject_arrow_comp (baseChangeQuotientMap g K)))
        (kernelSubobjectIso _).symm (kernelSubobject_arrow' _)))

/-- **The quotient of the base change is the pullback of the quotient.** For `g : T' ⟶ T` and a
submodule `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T`, the quotient of `𝒪^{⊕ r}` on `ℙⁿ_{T'}` by
`AlgebraicGeometry.ProjectiveQuot.baseChange g K` is the inverse image of `𝒪^{⊕ r} / K`, the
inverse image of the quotient map being an epimorphism. -/
def quotientBaseChangeIso {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    quotient (baseChange g K) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (quotient K) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (baseChangeIsColimit g K)

/-- The identification `AlgebraicGeometry.ProjectiveQuot.quotientBaseChangeIso` carries the
quotient map of the base change to the pulled-back quotient map. -/
@[reassoc (attr := simp)]
theorem quotientπ_quotientBaseChangeIso_hom {T' T : Scheme.{u}} (g : T' ⟶ T)
    (K : Subobject (freeModule n r T)) :
    quotientπ (baseChange g K) ≫ (quotientBaseChangeIso g K).hom = baseChangeQuotientMap g K :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (baseChangeIsColimit g K)
    WalkingParallelPair.one

/-- **Finite presentation and flatness over the base are stable under base change**: the base
change of a member of `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` is a member of `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T')`
(Stacks 01BQ, 01U8). -/
theorem baseChange_mem_families {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ families n r T) :
    baseChange g K ∈ families n r T' := by
  obtain ⟨hfp, hflat⟩ := hK
  have : (quotient K).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_of_isFinitePresentation (quotient K)
  exact ⟨Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (quotientBaseChangeIso g K).symm inferInstance,
    isFlatOver_of_moduleIso _
      (((Stacks.ProjectiveBundleQuotients.pullbackIso (projectiveSpaceOverMap n g)).app
        (quotient K)).symm ≪≫ (quotientBaseChangeIso g K).symm)
      (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ (isPullback_projectiveSpaceOverMap n g)
        (quotient K) ‹_› hflat)⟩

/-- The fibre of `ℙⁿ_{T'} ⟶ ℙⁿ_T` over a point `t' ∈ T'` factors through the extension of the
ground field `κ(g t') ⟶ κ(t')`. -/
theorem fibreMap_comp_projectiveSpaceOverMap {T' T : Scheme.{u}} (g : T' ⟶ T) (t' : T') :
    letI := (g.residueFieldMap t').hom.toAlgebra
    fibreMap n t' ≫ projectiveSpaceOverMap n g =
      projectiveSpaceFieldExtensionMap (T.residueField (g t')) (T'.residueField t') n ≫
        fibreMap n (g t') := by
  let := (g.residueFieldMap t').hom.toAlgebra
  rw [projectiveSpaceOverMap_comp, projectiveSpaceFieldExtensionMap,
    projectiveSpaceOverRingMap_eq, projectiveSpaceOverMap_comp,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rfl

/-- A module of finite presentation on projective space over a field is coherent. -/
theorem isCoherent_of_isFinitePresentation_projectiveSpace (k : Type u) [Field k]
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsFinitePresentation] : F.IsCoherent :=
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n _
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation F inferInstance

/-- **The fibre Hilbert polynomial is stable under base change**: the base change of a member of
`Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` is a member of `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T')`. The fibre of the base
change at `t'` is the extension of scalars of the fibre at `g t'` along `κ(g t') ⟶ κ(t')`, whose
Hilbert polynomial is unchanged. -/
@[ega "III 7.9.12" "7.9.12.3"]
theorem baseChange_mem_hilbertFamilies {P : Polynomial ℚ} {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    baseChange g K ∈ hilbertFamilies n r P T' := by
  obtain ⟨hfam, hP⟩ := hK
  refine ⟨baseChange_mem_families g hfam, fun t' => ?_⟩
  have := hfam.1
  have := (baseChange_mem_families g hfam).1
  obtain ⟨hcoh, hval⟩ := hP (g t')
  let := (g.residueFieldMap t').hom.toAlgebra
  let E := projectiveSpaceFieldExtensionMap (T.residueField (g t')) (T'.residueField t') n
  let G := Scheme.Modules.pullback (projectiveSpaceOverMap n g)
  let Q := quotient K
  -- The fibre of the pulled-back quotient is the field extension of the fibre.
  let e₁ : fibre t' (quotient (baseChange g K)) ≅ fibre t' (G.obj Q) :=
    (Scheme.Modules.pullback (fibreMap n t')).mapIso (quotientBaseChangeIso g K)
  let e₂ : fibre t' (G.obj Q) ≅ (Scheme.Modules.pullback E).obj (fibre (g t') Q) :=
    (Scheme.Modules.pullbackComp (fibreMap n t') (projectiveSpaceOverMap n g)).app Q ≪≫
      (Scheme.Modules.pullbackCongr (fibreMap_comp_projectiveSpaceOverMap g t')).app Q ≪≫
      ((Scheme.Modules.pullbackComp E (fibreMap n (g t'))).app Q).symm
  have : (fibre t' (quotient (baseChange g K))).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _ _
  have hFK : ((Scheme.Modules.pullback E).obj (fibre (g t') Q)).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _ _
  refine ⟨inferInstance, fun d => ?_⟩
  rw [hilbertPolynomial_eq_of_iso _ n (e₁ ≪≫ e₂) d,
    hilbertPolynomial_pullback_fieldExtension _ _ n (fibre (g t') Q) hFK d]
  exact hval d

end ProjectiveQuot

end AlgebraicGeometry

end

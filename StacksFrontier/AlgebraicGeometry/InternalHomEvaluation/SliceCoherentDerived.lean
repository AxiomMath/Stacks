module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence on a slice site, and the class it cuts out of the derived category

The dévissage behind the evaluation isomorphism of [Stacks, Tag 0A69] runs over the slice site
`C/V` of a ringed site, and every amplitude bound it applies is a bound for an object with
coherent cohomology. The objects it applies them to are produced in the course of the argument:
the class of a strictly perfect complex, the cone of a morphism out of one, and the truncations
of a restricted object. This file collects the coherence of all of them, on the slice site, with
no passage to an affine model.

Everything rests on two facts from the library and costs nothing beyond them:

* coherent sheaves of modules on a site form a weak Serre subcategory,
  `Stacks.SheafOfModules.Site.coherentModules_isWeakSerreClass`, and coherence restricts to a
  slice site, `Stacks.SheafOfModules.Site.isCoherent_over`;
* on a locally Noetherian scheme the structure sheaf is coherent,
  `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`.

## Main results

* `Stacks.SheafOfModules.Site.isCoherent_free_of_isCoherent_unit`: a finite free module is
  coherent as soon as the unit is.
* `Stacks.SheafOfModules.Site.isCoherent_of_isDirectSummandOfFiniteFree`: and so is a direct
  summand of one. This is the site form of
  `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`, which
  is stated for the modules of a locally Noetherian scheme and is what supplies the hypothesis
  on the unit here.
* `Stacks.SheafOfModules.Site.isCoherent_homology_of_isStrictlyPerfect`: the cohomology modules
  of a strictly perfect complex, [Stacks, Tag 08FL], are coherent.
* `Stacks.SheafOfModules.Site.isWeakSerre_coherentModules`: the five-term formulation of the
  weak Serre property, which is the form the derived-category closure theory consumes.
* `Stacks.SheafOfModules.Site.HasCoherentCohomology`, the class cut out of the derived category,
  with `hasCoherentCohomology_of_iso`, `hasCoherentCohomology_shift`,
  `hasCoherentCohomology_obj₂_of_distinguished` and
  `hasCoherentCohomology_obj₃_of_distinguished`: closed under isomorphism, under the shift, and
  two-out-of-three in a distinguished triangle — in particular at the cone of a morphism.
* `Stacks.SheafOfModules.Site.hasCoherentCohomology_Q_of_isStrictlyPerfect`: the class of a
  strictly perfect complex has coherent cohomology.
* `Stacks.SheafOfModules.Site.isCoherent_unit_over` and
  `Stacks.SheafOfModules.Site.hasCoherentCohomology_truncLE`,
  `hasCoherentCohomology_truncGE`: the hypothesis on the unit over an open of a locally
  Noetherian scheme, and stability of the class under the two truncations.

## The proofs

A finite free module is a finite coproduct of copies of the unit, and the coherent modules are
closed under finite coproducts. A direct summand of it is a quotient of a finite free module,
hence of finite type, and a subobject of one, so [Stacks, Tag 01BY] (1) applies. The cohomology
of a complex is a cokernel of a map into a kernel, so it lies in any weak Serre subcategory
containing the terms. On derived categories the closure theory of
`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory` takes over: a distinguished
triangle gives a five-term exact sequence of cohomology modules, and the third vertex is reached
by rotating.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules.Site

attribute [local instance] HasDerivedCategory.standard

section Modules

variable {C : Type u} [Category.{u} C] [HasFiniteWidePullbacks C] [HasBinaryProducts C]
  [HasPullbacks C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite free module is coherent as soon as the unit is.** The free module on a finite
index type is the coproduct of that many copies of the unit, and the coherent modules on a site
are closed under finite coproducts. -/
theorem isCoherent_free_of_isCoherent_unit
    (hR : IsCoherent.{u, u, u} (_root_.SheafOfModules.unit R)) (I : Type u) [Finite I] :
    IsCoherent.{u, u, u} (_root_.SheafOfModules.free (R := R) I) := by
  have hc := isCoherent_sigma (R := R) (fun _ : I => _root_.SheafOfModules.unit R) fun _ => hR
  refine (coherentModules R).prop_of_iso ?_ hc
  exact IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct fun _ : I => _root_.SheafOfModules.unit R)
    (_root_.SheafOfModules.isColimitFreeCofan (R := R) I)

/-- **A direct summand of a finite free module is coherent as soon as the unit is.** The
retraction exhibits it as a quotient of a finite free module, hence of finite type, and the
section exhibits it as a subobject of one, so [Stacks, Tag 01BY] (1) applies.

This is the site form of
`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`, which is
stated for the modules of a locally Noetherian scheme; `isCoherent_unit_over` below supplies the
hypothesis on the unit over an open of such a scheme. -/
theorem isCoherent_of_isDirectSummandOfFiniteFree
    (hR : IsCoherent.{u, u, u} (_root_.SheafOfModules.unit R)) (F : _root_.SheafOfModules.{u} R)
    (hF : _root_.IsDirectSummandOfFiniteFree R F) : IsCoherent.{u, u, u} F := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R F).mp hF
  have hfree := isCoherent_free_of_isCoherent_unit hR (ULift.{u} (Fin n))
  have hsm : IsSplitMono i := IsSplitMono.mk' ⟨r, hir⟩
  have hse : IsSplitEpi r := IsSplitEpi.mk' ⟨i, hir⟩
  have : Mono i := IsSplitMono.mono i (hf := hsm)
  have : Epi r := IsSplitEpi.epi r (hf := hse)
  have hft : F.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} r
      (IsCoherent.isFiniteType (M := _root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n))))
  exact isCoherent_of_mono i hft

/-- **The cohomology modules of a strictly perfect complex are coherent**, as soon as the unit
is. The terms are direct summands of finite free modules, and the cohomology of a complex is a
cokernel of a map into a kernel of maps between its terms, both of which a weak Serre
subcategory is closed under. -/
theorem isCoherent_homology_of_isStrictlyPerfect
    (hR : IsCoherent.{u, u, u} (_root_.SheafOfModules.unit R))
    (P : CochainComplex (_root_.SheafOfModules.{u} R) ℤ) (hP : _root_.IsStrictlyPerfect R P)
    (n : ℤ) : IsCoherent.{u, u, u} (P.homology n) :=
  ObjectProperty.prop_homology (coherentModules R) P n fun m =>
    isCoherent_of_isDirectSummandOfFiniteFree hR (P.X m) (hP.termDirectSummand m)

/-- **The five-term formulation of the weak Serre property for coherent modules on a site**: in
an exact sequence of five terms whose four outer terms are coherent, the middle one is. This is
the shape the derived-category closure theory of
`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory` consumes. -/
@[sga "6 I 3.4" "special case", sga "6 IV 2.4" "more general"]
theorem isWeakSerre_coherentModules :
    WeakSerre.IsWeakSerre (fun M : _root_.SheafOfModules.{u} R => IsCoherent.{u, u, u} M) := by
  refine ⟨inferInstance,
    ObjectProperty.exists_prop_of_isWeakSerreClass
      (fun M : _root_.SheafOfModules.{u} R => IsCoherent.{u, u, u} M),
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact ObjectProperty.prop_mid_of_exact₄
    (ObjectProperty.prop_obj₂_of_exact
      (P := fun M : _root_.SheafOfModules.{u} R => IsCoherent.{u, u, u} M))
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

end Modules

section Derived

variable {C : Type u} [Category.{u} C] [HasFiniteWidePullbacks C] [HasBinaryProducts C]
  [HasPullbacks C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An object of the derived category of modules on a site has coherent cohomology** when
every one of its cohomology modules is coherent. This is the condition cutting `D_Coh(O)` out of
`D(O)`, written on an arbitrary site so that it can be read on a slice site. -/
def HasCoherentCohomology (E : DerivedCategory (_root_.SheafOfModules.{u} R)) : Prop :=
  ∀ n : ℤ, IsCoherent.{u, u, u}
    ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} R) n).obj E)

omit [HasFiniteWidePullbacks C] [HasBinaryProducts C] [HasPullbacks C]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `HasCoherentCohomology` is `DerivedCategoryB.derivedCategoryB` at the coherent modules; this
records the identification, which is how the closure theory applies. -/
theorem hasCoherentCohomology_iff (E : DerivedCategory (_root_.SheafOfModules.{u} R)) :
    HasCoherentCohomology E ↔ DerivedCategoryB.derivedCategoryB (coherentModules R) E :=
  Iff.rfl

/-- Having coherent cohomology is invariant under isomorphism. -/
theorem hasCoherentCohomology_of_iso {E E' : DerivedCategory (_root_.SheafOfModules.{u} R)}
    (e : E ≅ E') (hE : HasCoherentCohomology E) : HasCoherentCohomology E' :=
  (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms (coherentModules R)
    isWeakSerre_coherentModules).of_iso e hE

/-- Having coherent cohomology is stable under the shift. -/
theorem hasCoherentCohomology_shift (a : ℤ)
    {E : DerivedCategory (_root_.SheafOfModules.{u} R)} (hE : HasCoherentCohomology E) :
    HasCoherentCohomology ((shiftFunctor (DerivedCategory (_root_.SheafOfModules.{u} R)) a).obj
      E) :=
  DerivedCategoryB.derivedCategoryB_shift_mem (coherentModules R) isWeakSerre_coherentModules a hE

/-- **Two out of three in a distinguished triangle, at the middle vertex.** -/
theorem hasCoherentCohomology_obj₂_of_distinguished
    (T : Triangle (DerivedCategory (_root_.SheafOfModules.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : HasCoherentCohomology T.obj₁) (h₃ : HasCoherentCohomology T.obj₃) :
    HasCoherentCohomology T.obj₂ :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished (coherentModules R)
    isWeakSerre_coherentModules T hT h₁ h₃

/-- **Two out of three in a distinguished triangle, at the third vertex.** In particular the cone
of a morphism between objects with coherent cohomology has coherent cohomology: rotating the
triangle puts the cone in the middle, with the shift of the first vertex third. -/
theorem hasCoherentCohomology_obj₃_of_distinguished
    (T : Triangle (DerivedCategory (_root_.SheafOfModules.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : HasCoherentCohomology T.obj₁) (h₂ : HasCoherentCohomology T.obj₂) :
    HasCoherentCohomology T.obj₃ :=
  hasCoherentCohomology_obj₂_of_distinguished T.rotate (rot_of_distTriang T hT) h₂
    (hasCoherentCohomology_shift 1 h₁)

/-- **The class of a strictly perfect complex has coherent cohomology**, as soon as the unit is
coherent: its cohomology in the derived category is the cohomology of the complex. -/
theorem hasCoherentCohomology_Q_of_isStrictlyPerfect
    (hR : IsCoherent.{u, u, u} (_root_.SheafOfModules.unit R))
    (P : CochainComplex (_root_.SheafOfModules.{u} R) ℤ) (hP : _root_.IsStrictlyPerfect R P) :
    HasCoherentCohomology (DerivedCategory.Q.obj P) := fun n =>
  (coherentModules R).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors (_root_.SheafOfModules.{u} R) n).symm.app P)
    (isCoherent_homology_of_isStrictlyPerfect hR P hP n)

omit [HasPullbacks C]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Having coherent cohomology survives the canonical truncation from above.** In the degrees
it retains, `τ_{≤ a} E` has the cohomology of `E`; above them it has none. -/
theorem hasCoherentCohomology_truncLE {E : DerivedCategory (_root_.SheafOfModules.{u} R)}
    (hE : HasCoherentCohomology E) (a : ℤ) :
    HasCoherentCohomology ((DerivedCategory.TStructure.t.truncLE a).obj E) := fun n =>
  DerivedCategory.prop_homologyFunctor_truncLE_obj (coherentModules R) E hE a n

omit [HasPullbacks C]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Having coherent cohomology survives the canonical truncation from below.** -/
theorem hasCoherentCohomology_truncGE {E : DerivedCategory (_root_.SheafOfModules.{u} R)}
    (hE : HasCoherentCohomology E) (a : ℤ) :
    HasCoherentCohomology ((DerivedCategory.TStructure.t.truncGE a).obj E) := fun n =>
  DerivedCategory.prop_homologyFunctor_truncGE_obj (coherentModules R) E hE a n

omit [HasBinaryProducts C] in
/-- **Having coherent cohomology survives restriction to a slice site.** Restriction is exact,
so it commutes with cohomology, and coherence restricts to a slice site by
`Stacks.SheafOfModules.Site.isCoherent_over`. -/
theorem hasCoherentCohomology_overFunctor (W : C)
    [(_root_.SheafOfModules.overFunctor.{u} R W).Additive]
    [PreservesFiniteLimits (_root_.SheafOfModules.overFunctor.{u} R W)]
    [PreservesFiniteColimits (_root_.SheafOfModules.overFunctor.{u} R W)]
    {E : DerivedCategory (_root_.SheafOfModules.{u} R)} (hE : HasCoherentCohomology E) :
    HasCoherentCohomology
      ((_root_.SheafOfModules.overFunctor.{u} R W).mapDerivedCategory.obj E) := fun n =>
  have := hE n
  (coherentModules (R.over W)).prop_of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (_root_.SheafOfModules.overFunctor.{u} R W) n).app E).symm
    (isCoherent_over W)

end Derived

section Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The structure sheaf of a locally Noetherian scheme is coherent on every slice site.** This
is [Stacks, Tag 01XZ] for `𝒪_X` followed by `Stacks.SheafOfModules.Site.isCoherent_over`; it is
the hypothesis on the unit that every statement above takes. -/
theorem isCoherent_unit_over (W : X.Opens) :
    IsCoherent.{u, u, u} (_root_.SheafOfModules.unit (X.ringCatSheaf.over W)) :=
  (coherentModules (X.ringCatSheaf.over W)).prop_of_iso
    (Stacks.SheafOfModules.overFunctorUnitIso X.ringCatSheaf W).symm
    (isCoherent_over_of_isCoherent_opens
      (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X).stacksIsCoherent W)

end Scheme

end Stacks.SheafOfModules.Site

end

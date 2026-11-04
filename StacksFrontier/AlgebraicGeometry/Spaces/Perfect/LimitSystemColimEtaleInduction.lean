module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.CanonicalSystem
public import StacksFrontier.CategoryTheory.PullbackData.LimitSystemColimShift

/-!
# The étale dévissage of Stacks 09RI

In Situation 09RH let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  The conclusion of Stacks 09RI is
that

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective, which for the stages read as a system over `X₀` is
`CategoryTheory.PullbackData.LimitSystem.IsColim` and for the canonical system of derived
pullbacks is `AlgebraicGeometry.Space.DescentSituation.IsHomColimit`.

This file runs the dévissage of the source's proof: the induction principle of Stacks 08GP over
the quasi-compact quasi-separated objects of `(X₀)_{spaces, étale}`.  Following the
treatment of the relative tag 0DKV in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/`
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativelyPerfectHomDescentInduction.lean`,
the induction is carried out on `X₀` alone: for an étale `w : W ⟶ X₀` the predicate is the
colimit statement for the *object* `w_!(w^*E₀)` of `D(𝒪_{X₀})`, at every shift, so that the
system itself never moves and the Mayer–Vietoris step is closure of the predicate under
distinguished triangles in its first argument.  The conclusion is that the tag holds for
`(E₀, K₀)` as soon as it holds for `(u_!(u^*E₀), K₀)` at every shift for every étale
`u : U ⟶ X₀` with `U` affine — the affine case, which this file does not discharge.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.ExtendRestrictIsColim`: the predicate of the
  induction, the colimit statement for `w_!(w^*E₀)` at every shift.

## Main results

* the additivity of `CategoryTheory.PullbackData.pull` as an instance, and
  `smallEtaleDerivedPullbackData_pull_isTriangulated`: the derived pullback of Stacks 06YY is
  additive and triangulated, at the spelling `CategoryTheory.PullbackData.pull` of the
  pseudofunctor datum.
* `AlgebraicGeometry.Space.DescentSituation.extendRestrictIsColim_of_eds`: **the
  Mayer–Vietoris step**, from Stacks 08GV on `W` pushed to `X₀` by extension by zero and the
  five lemma `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.obj₃`.
* `AlgebraicGeometry.Space.DescentSituation.extendRestrictIsColim_of_qcqs`: **the induction**,
  Stacks 08GP over the étale objects of a quasi-compact quasi-separated algebraic space étale
  over `X₀`.
* `AlgebraicGeometry.Space.DescentSituation.isColim_of_affine` and
  `isHomColimit_canonicalDerivedPullbackSystem_of_affine`: **Stacks 09RI reduced to its affine
  case**, in the two equivalent forms.

## Implementation notes

The shifts are quantified *inside* the induction predicate, as they are in both existing
templates — `AlgebraicGeometry.Space.RelativeDescentSituation.ShiftedHomDescent` for 0DKV and
`Stacks.LimitHomDescent.SchemeSystem.RestrictIsColim` for the scheme-level 09RE.  The five lemma
`CategoryTheory.PullbackData.LimitSystem.IsColim.obj₃` needs the statement at `A₁`, `A₂`, `A₁⟦1⟧`
and `A₂⟦1⟧`, and a predicate with the shift outside cannot supply the last two.

The derived pullback of Stacks 06YY is additive and triangulated at the spelling
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, but
`CategoryTheory.PullbackData.pull` of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` is a field projection through a `def`,
which instance resolution does not unfold; the two instances below restate those facts at the
projection, exactly as
`AlgebraicGeometry.Space.ComplexesSituation.smallEtaleDerivedPullbackData_pull_commShift` already
restates the compatibility with the shift.

## Where the two universe restrictions of Stacks 09RI live

Nothing below restricts the index: `I` is an arbitrary directed preorder in an arbitrary
universe `v`, and no bound on its cardinality is assumed.  The dévissage of the tag — the
induction principle of Stacks 08GP and the Mayer–Vietoris step of Stacks 08GV — needs neither.

Both restrictions the tag's proof carries belong to the affine case, which is the hypothesis
`hleaf` here and not discharged.  The degreewise colimit clauses of the affine dictionary are
proved only for `I : Type u`, in
`StacksFrontier/Homology/HomotopyCategory/FilteredColimitHomDegreewise.lean`,
and the free form is refuted by
`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`; and the geometric
input `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/GlobalFunctionsColimit.lean` carries the bound
`#I < B.cutoff.ord.cof` of Stacks 07SI, whose necessity is refuted by
`AlgebraicGeometry.Space.Refute07SI.not_forall_isSectionsColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`.
Both are inputs of the source — Situation 09RD's index set lives in the universe of the spaces,
and the site is closed under the limits it forms — not weakenings of the tag.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits etaleModuleLowerShriek_additive
  preservesFiniteLimits_etaleModuleLowerShriek preservesFiniteColimits_etaleModuleLowerShriek

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The derived pullback of `𝒪`-modules along a morphism of algebraic spaces is additive, at the
spelling `CategoryTheory.PullbackData.pull` of the pseudofunctor datum.

The statement itself is the base's
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_pull_additive`
(`StacksFrontier/AlgebraicGeometry/Quot/RelHomStructureRepresentable.lean`), which is a `theorem` and
so is not found by instance search; this is the instance wrapper, and it is deliberately anonymous
so as not to shadow that name. -/
instance {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : ((smallEtaleDerivedPullbackData B S hS).pull f).Additive :=
  haveI := hasDerivedModulePullbacks B S hS f
  inferInstanceAs (smallEtaleDerivedModulePullback B S hS f).Additive

/-- **Stacks 06YY, exactness**, at the spelling `CategoryTheory.PullbackData.pull` of the
pseudofunctor datum: the derived pullback of `𝒪`-modules along a morphism of algebraic spaces is
triangulated. -/
instance smallEtaleDerivedPullbackData_pull_isTriangulated {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : ((smallEtaleDerivedPullbackData B S hS).pull f).IsTriangulated :=
  haveI := hasDerivedModulePullbacks B S hS f
  isTriangulated_smallEtaleDerivedModulePullback B S hS f

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The predicate of the dévissage of Stacks 09RI.**  For an étale morphism `w : W ⟶ X₀` of
algebraic spaces, the colimit statement of the tag for the object `w_!(w^*E₀)` of `D(𝒪_{X₀})`
against `K₀`, at every shift of the first argument. -/
def ExtendRestrictIsColim (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    {W : AlgebraicSpaces B S hS} (w : W ⟶ D.stage D.base) (hw : IsEtale B S hS w.hom) : Prop :=
  D.limitSystem.ShiftedIsColim (smallEtaleDerivedPullbackData B S hS)
    ((etaleModuleExtendRestrict B S hS w hw).mapDerivedCategory.obj E₀) K₀

variable {D}

/-- The predicate depends only on the morphism `w`, not on the proof that it is étale. -/
theorem extendRestrictIsColim_congr {E₀ K₀ : derivedModules B S hS (D.stage D.base)}
    {W : AlgebraicSpaces B S hS} {w w' : W ⟶ D.stage D.base} (hw : IsEtale B S hS w.hom)
    (hw' : IsEtale B S hS w'.hom) (h : w = w')
    (hE : D.ExtendRestrictIsColim E₀ K₀ w hw) : D.ExtendRestrictIsColim E₀ K₀ w' hw' := by
  subst h
  exact hE

/-- **The Mayer–Vietoris step of the dévissage of Stacks 09RI.**  Let `w : W ⟶ X₀` be étale and
let `(U ⊆ W, V ⟶ W)` be an elementary distinguished square with intersection `U ×_W V`.  If the
predicate holds for the three composites `j ≫ w`, for `j` from `U`, from `V` and from `U ×_W V`,
then it holds for `w`.

Extension by zero along `w` carries the Mayer–Vietoris triangle of Stacks 08GV on `W` to a
distinguished triangle of `D(𝒪_{X₀})` whose three objects are the objects `(j ≫ w)_!((j ≫ w)^*E₀)`
attached to the three pieces, and the predicate is closed under distinguished triangles in its
first argument. -/
theorem extendRestrictIsColim_of_eds {W : AlgebraicSpaces B S hS} (w : W ⟶ D.stage D.base)
    (hw : IsEtale B S hS w.hom) {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1}
    {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hU : D.ExtendRestrictIsColim E₀ K₀ (edsOpenHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) hw))
    (hV : D.ExtendRestrictIsColim E₀ K₀ (edsEtaleHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) hw))
    (hP : D.ExtendRestrictIsColim E₀ K₀ (edsInterHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq) hw)) :
    D.ExtendRestrictIsColim E₀ K₀ w hw := by
  obtain ⟨δ, hT⟩ := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).2
    ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj E₀)
  have hT' := (etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.map_distinguished _ hT
  have hcoh := smallEtaleDerivedPullbackData_isCoherent B S hS
  have f : ∀ {Y : AlgebraicSpaces B S hS} (j : Y ⟶ W) (hj : IsEtale B S hS j.hom),
      D.ExtendRestrictIsColim E₀ K₀ (j ≫ w) (isEtale_comp B S hS hj hw) →
        D.limitSystem.ShiftedIsColim (smallEtaleDerivedPullbackData B S hS)
          ((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.obj
            ((etaleModuleExtendRestrict B S hS j hj).mapDerivedCategory.obj
              ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj E₀))) K₀ :=
    fun j hj h ↦ PullbackData.LimitSystem.ShiftedIsColim.of_iso hcoh
      ((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.mapIso
          ((Dualizing.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS w hw)
            (etaleModuleExtendRestrict B S hS j hj)).app E₀).symm ≪≫
        ((Dualizing.mapDerivedCategoryComp
          (etaleModulePullback.{u, u} B S hS w hw ⋙ etaleModuleExtendRestrict B S hS j hj)
          (etaleModuleLowerShriek B S hS w hw)).app E₀).symm ≪≫
        (Dualizing.mapDerivedCategoryNatIso _ _
          (etaleModuleExtendRestrictCompIso B S hS j w hj hw
            (isEtale_comp B S hS hj hw))).app E₀).symm h
  refine PullbackData.LimitSystem.ShiftedIsColim.of_iso hcoh
    ((Dualizing.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS w hw)
      (etaleModuleLowerShriek B S hS w hw)).app E₀).symm
    (PullbackData.LimitSystem.ShiftedIsColim.obj₃ hcoh _ hT' K₀ ?_ ?_)
  · exact f _ (isEtale_edsInterHom B S hS hsq) hP
  · exact PullbackData.LimitSystem.ShiftedIsColim.obj₂ hcoh _
      ((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.map_distinguished _
        (binaryBiproductTriangle_distinguished _ _)) K₀
      (f _ (isEtale_edsOpenHom B S hS hsq) hU) (f _ (isEtale_edsEtaleHom B S hS hsq) hV)

/-- **The induction of Stacks 08GP for the dévissage of Stacks 09RI.**  Let `v : X' ⟶ X₀` be
étale with `X'` quasi-compact and quasi-separated.  If the predicate holds for `h ≫ v` for every
étale `h : U ⟶ X'` with `U` affine, then it holds for `v`. -/
theorem extendRestrictIsColim_of_qcqs (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    {X' : AlgebraicSpaces B S hS} (v : X' ⟶ D.stage D.base) (hv : IsEtale B S hS v.hom)
    (hX'qc : IsQuasiCompactSpace B S hS X'.1)
    (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
    (hleaf : ∀ {U : AlgebraicSpaces B S hS} (h : U ⟶ X') (hh : IsEtale B S hS h.hom),
      IsAffineSpace B S hS U.1 →
        D.ExtendRestrictIsColim E₀ K₀ (h ≫ v) (isEtale_comp B S hS hh hv)) :
    D.ExtendRestrictIsColim E₀ K₀ v hv := by
  let Q : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X'.1) → Prop := fun Y g ↦
    ∀ (hY : IsAlgebraicSpace B S hS Y) (hg : IsEtale B S hS g),
      D.ExtendRestrictIsColim E₀ K₀
        ((ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X') ≫ v)
        (isEtale_comp B S hS hg hv)
  have key : Q X'.1 (𝟙 X'.1) := by
    refine qcqs_induction_on_self B S hS hZ X' hX'qc hX'qs Q ?_ ?_
    · intro V hV hY hg
      exact hleaf (U := ⟨V.1.left.1, hY⟩) (ObjectProperty.homMk V.1.hom.hom) hg hV
    · intro W V Uo f hf hsq _ _ _ _ hQU hQV hQP hY hg
      refine extendRestrictIsColim_of_eds (W := W.1.left)
        (ObjectProperty.homMk W.1.hom.hom ≫ v) (isEtale_comp B S hS hg hv) hsq E₀ K₀ ?_ ?_ ?_
      · exact extendRestrictIsColim_congr _ _ rfl
          (hQU hsq.isOpenSubspace.1 (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) hg))
      · refine extendRestrictIsColim_congr _ _ ?_ (hQV hsq.isAlgebraicSpace V.2)
        ext1
        exact hf.symm =≫ v.hom
      · exact extendRestrictIsColim_congr _ _ rfl
          (hQP (edsInter B S hS hsq).2
            (isEtale_comp B S hS (isEtale_edsFst B S hS hsq)
              (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) hg)))
  exact extendRestrictIsColim_congr _ _ (Category.id_comp v)
    (key X'.2 fun _ _ hφ ↦ by simpa using hφ)

/-- For the identity of `X₀` the object `w_!(w^*E₀)` is `E₀`, so the colimit statement for
`(E₀, K₀)` follows from the predicate at the identity. -/
theorem isColim_of_extendRestrictIsColim_id {E₀ K₀ : derivedModules B S hS (D.stage D.base)}
    (h : IsEtale B S hS (𝟙 (D.stage D.base) : D.stage D.base ⟶ D.stage D.base).hom)
    (hE : D.ExtendRestrictIsColim E₀ K₀ (𝟙 (D.stage D.base)) h) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  have hcoh := smallEtaleDerivedPullbackData_isCoherent B S hS
  exact (PullbackData.LimitSystem.ShiftedIsColim.of_iso hcoh
    ((Dualizing.mapDerivedCategoryNatIso _ _
      (etaleModuleExtendRestrictIdIso B S hS (D.stage D.base) h)).app E₀ ≪≫
      (Functor.mapDerivedCategoryIdIso
        (C := Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)).app E₀)
    hE 0).of_iso_fst hcoh ((shiftFunctorZero _ ℤ).app E₀)

/-- **Stacks 09RI, reduced to its affine case.**  In Situation 09RH, if for every étale
`u : U ⟶ X₀` with `U` affine the colimit statement holds for `u_!(u^*E₀)` against `K₀` at every
shift, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective. -/
theorem isColim_of_affine (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hleaf : ∀ {U : AlgebraicSpaces B S hS} (u : U ⟶ D.stage D.base)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS U.1 →
        D.ExtendRestrictIsColim E₀ K₀ u hu) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  have hid : IsEtale B S hS
      (𝟙 (D.stage D.base) : D.stage D.base ⟶ D.stage D.base).hom :=
    fun _ _ hφ ↦ by simpa using hφ
  exact isColim_of_extendRestrictIsColim_id hid
    (extendRestrictIsColim_of_qcqs E₀ K₀ (𝟙 (D.stage D.base)) hid
      (D.quasiCompact D.base) (D.quasiSeparated D.base)
      fun h hh hU ↦ hleaf (h ≫ 𝟙 (D.stage D.base)) (isEtale_comp B S hS hh hid) hU)

/-- **The conclusion of Stacks 09RI for the canonical system of derived pullbacks, reduced to
its affine case.** -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_affine
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hleaf : ∀ {U : AlgebraicSpaces B S hS} (u : U ⟶ D.stage D.base)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS U.1 →
        D.ExtendRestrictIsColim E₀ K₀ u hu) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  (isHomColimit_canonicalDerivedPullbackSystem_iff D E₀ K₀).2 (isColim_of_affine E₀ K₀ hleaf)

end DescentSituation

end AlgebraicGeometry.Space

end

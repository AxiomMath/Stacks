module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.EqualizerOverAnAtlas

/-!
# Global regular functions of an algebraic space as an equalizer over a chart

Let `F` be a presheaf on the big fppf site of a scheme `S`, let `U` be an étale chart of `F`
whose one-element family covers the final object of the small étale site, and let
`a, b : V ⟶ U` be two morphisms of charts exhibiting `V` as the kernel pair `U ×_F U`. Then the
ring

`AlgebraicGeometry.Space.globalFunctions B S hS F`

of global regular functions of `F` is the equalizer of the two restriction maps

`Γ(U, 𝒪_U) ⇉ Γ(V, 𝒪_V)`,

the comparison being restriction of a global function to the chart `U`.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsRestriction`: restriction of regular functions along a
  morphism of étale charts, as a ring homomorphism.
* `AlgebraicGeometry.Space.globalFunctionsToEqualizer`: restriction of global regular functions
  to a chart, landing in the equalizer of the two restrictions to a kernel pair.
* `AlgebraicGeometry.Space.globalFunctionsEqualizerRingEquiv`: the ring of global functions is
  isomorphic to the subring of `Γ(U, 𝒪_U)` on which the two restrictions to the kernel pair
  agree.

## Main results

* `AlgebraicGeometry.Space.factorsPairs_of_isPullback`: the two projections of a kernel pair of
  a chart factor every pair of morphisms of charts into that chart
  (`CategoryTheory.Presheaf.FactorsPairs`).
* `AlgebraicGeometry.Space.isSheaf_structurePresheaf_forget`: the structure presheaf of the
  small étale site is a sheaf of sets (`CategoryTheory.Presheaf.IsSheaf`).
* `AlgebraicGeometry.Space.bijective_globalFunctionsToEqualizer`: restriction to a covering chart
  is a bijection of the global regular functions onto the equalizer of the two restrictions to a
  kernel pair.

## References

* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Restriction of regular functions along a morphism of étale charts of `F`, as a ring
homomorphism.  This is the restriction map of the structure presheaf of the small étale site,
read as a map of the rings of global regular functions of the underlying schemes. -/
abbrev chartSectionsRestriction {U V : SmallEtale B S hS F} (a : V ⟶ U) :
    Γ(chartScheme U, ⊤) →+* Γ(chartScheme V, ⊤) :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map a)).op).hom

/-- Let `U` be an étale chart of `F` and let `a, b : V ⟶ U` be two morphisms of charts whose
underlying square of presheaves exhibits `V` as the fibre product `U ×_F U`. Then every pair of
morphisms of charts into `U` is obtained from `a` and `b` by precomposition with a single
morphism. -/
theorem factorsPairs_of_isPullback {U V : SmallEtale B S hS F} (a b : V ⟶ U)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS F).map a))
      (yoneda.map ((SmallEtale.toOver B S hS F).map b)) U.obj.hom U.obj.hom) :
    CategoryTheory.Presheaf.FactorsPairs a b := by
  intro Z f g
  have hw : ∀ {A C : SmallEtale B S hS F} (c : A ⟶ C),
      yoneda.map ((SmallEtale.toOver B S hS F).map c) ≫ C.obj.hom = A.obj.hom :=
    fun c => CostructuredArrow.w c.hom
  let φ : yoneda.obj ((SmallEtale.toOver B S hS F).obj Z) ⟶
      yoneda.obj ((SmallEtale.toOver B S hS F).obj V) :=
    hsq.lift (yoneda.map ((SmallEtale.toOver B S hS F).map f))
      (yoneda.map ((SmallEtale.toOver B S hS F).map g)) ((hw f).trans (hw g).symm)
  let h₀ : (SmallEtale.toOver B S hS F).obj Z ⟶ (SmallEtale.toOver B S hS F).obj V :=
    yoneda.preimage φ
  have hh₀ : yoneda.map h₀ = φ := yoneda.map_preimage φ
  have key : ∀ (c : V ⟶ U) (k : Z ⟶ U),
      φ ≫ yoneda.map ((SmallEtale.toOver B S hS F).map c) =
        yoneda.map ((SmallEtale.toOver B S hS F).map k) →
      h₀ ≫ (SmallEtale.toOver B S hS F).map c = (SmallEtale.toOver B S hS F).map k :=
    fun c k h => yoneda.map_injective (by rw [Functor.map_comp, hh₀, h])
  have ha := key a f (hsq.lift_fst _ _ _)
  have hb := key b g (hsq.lift_snd _ _ _)
  have hV : yoneda.map h₀ ≫ V.obj.hom = Z.obj.hom := by
    rw [← hw a, ← Category.assoc, ← Functor.map_comp, ha, hw f]
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk h₀ hV), ?_, ?_⟩
  · exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ha)
  · exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hb)

/-- The structure presheaf of the small étale site of `F`, read as a presheaf of sets, is a
sheaf. -/
theorem isSheaf_structurePresheaf_forget :
    CategoryTheory.Presheaf.IsSheaf (SmallEtale.topology B S hS F)
      (structurePresheaf B S hS F ⋙ CategoryTheory.forget CommRingCat.{u}) :=
  (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_globalSections B S hS F)

variable {B S hS F}

/-- A global regular function of `F` restricted to the chart `U` lies in the equalizer of the
two restrictions to a kernel pair of `U`. -/
theorem chartSectionsRestriction_mem_eqLocus (X : AlgebraicSpaces B S hS)
    {U V : SmallEtale B S hS X.obj} (a b : V ⟶ U) (s : globalFunctions B S hS X.obj) :
    globalFunctionsChartRestriction B S hS X U s ∈
      RingHom.eqLocus (chartSectionsRestriction B S hS X.obj a)
        (chartSectionsRestriction B S hS X.obj b) := by
  have ha := congrFun (globalFunctionsChartRestriction_naturality B S hS X a) s
  have hb := congrFun (globalFunctionsChartRestriction_naturality B S hS X b) s
  exact ha.trans hb.symm

/-- Restriction of global regular functions to a chart, landing in the equalizer of the two
restrictions to a kernel pair of that chart. -/
def globalFunctionsToEqualizer (X : AlgebraicSpaces B S hS)
    {U V : SmallEtale B S hS X.obj} (a b : V ⟶ U) :
    globalFunctions B S hS X.obj →+*
      RingHom.eqLocus (chartSectionsRestriction B S hS X.obj a)
        (chartSectionsRestriction B S hS X.obj b) :=
  (globalFunctionsChartRestriction B S hS X U).codRestrict _
    (chartSectionsRestriction_mem_eqLocus X a b)

/-- Let `X` be an algebraic space over `S`, let `U` be an étale chart whose one-element family
covers the final object of the small étale site, and let `a, b : V ⟶ U` exhibit `V` as the
kernel pair `U ×_X U`. Then restriction to `U` is a bijection of the ring of global regular
functions of `X` onto the subring of `Γ(U, 𝒪_U)` on which the two restrictions to `V` agree. -/
theorem bijective_globalFunctionsToEqualizer (X : AlgebraicSpaces B S hS)
    {U V : SmallEtale B S hS X.obj} (a b : V ⟶ U)
    (hcov : (SmallEtale.topology B S hS X.obj).CoversTop (fun _ : Unit => U))
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.obj).map a))
      (yoneda.map ((SmallEtale.toOver B S hS X.obj).map b)) U.obj.hom U.obj.hom) :
    Function.Bijective (globalFunctionsToEqualizer X a b) := by
  classical
  set P := structurePresheaf B S hS X.obj ⋙ CategoryTheory.forget CommRingCat.{u}
  have hsheaf := isSheaf_structurePresheaf_forget B S hS X.obj
  have hrel := factorsPairs_of_isPullback B S hS X.obj a b hsq
  let ε : globalFunctions B S hS X.obj ≃ CategoryTheory.Presheaf.globalSections P :=
    (CategoryTheory.Presheaf.globalSectionsEquivSections P).symm
  have hev : ∀ s : globalFunctions B S hS X.obj,
      CategoryTheory.Presheaf.globalSectionsEval P U (ε s) =
        globalFunctionsChartRestriction B S hS X U s := by
    intro s
    rw [CategoryTheory.Presheaf.globalSectionsEval_def]
    show ((CategoryTheory.Presheaf.globalSectionsEquivSections P)
      ((CategoryTheory.Presheaf.globalSectionsEquivSections P).symm s)).1 (op U) = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨fun s t hst => ?_, fun y => ?_⟩
  · exact ε.injective (CategoryTheory.Presheaf.globalSectionsEval_injective P hsheaf hcov
      ((hev s).trans ((congrArg Subtype.val hst).trans (hev t).symm)))
  · obtain ⟨g, hg⟩ := CategoryTheory.Presheaf.exists_globalSectionsEval_eq P hsheaf hcov hrel
      (y : Γ(chartScheme U, ⊤)) y.2
    exact ⟨ε.symm g, Subtype.ext <| (hev (ε.symm g)).symm.trans <| by
      rw [Equiv.apply_symm_apply, hg]⟩

/-- The equalizer presentation of the ring of global regular functions, as a ring
isomorphism: for an étale chart `U` covering the final object of the small étale site and a
kernel pair `a, b : V ⟶ U` of it, restriction to `U` identifies the global regular functions of
`X` with the subring of `Γ(U, 𝒪_U)` on which the two restrictions to `V` agree. -/
def globalFunctionsEqualizerRingEquiv (X : AlgebraicSpaces B S hS)
    {U V : SmallEtale B S hS X.obj} (a b : V ⟶ U)
    (hcov : (SmallEtale.topology B S hS X.obj).CoversTop (fun _ : Unit => U))
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.obj).map a))
      (yoneda.map ((SmallEtale.toOver B S hS X.obj).map b)) U.obj.hom U.obj.hom) :
    globalFunctions B S hS X.obj ≃+*
      RingHom.eqLocus (chartSectionsRestriction B S hS X.obj a)
        (chartSectionsRestriction B S hS X.obj b) :=
  RingEquiv.ofBijective _ (bijective_globalFunctionsToEqualizer X a b hcov hsq)

end AlgebraicGeometry.Space

end

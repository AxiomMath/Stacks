module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Cohomology of modules is invariant under an equivalence of sites

Let `e : C' ≌ C` be an equivalence of categories which is continuous in both directions for
topologies `J'` on `C'` and `J` on `C`, and let `R` be a sheaf of rings on `(C, J)`. Restriction
along `e.functor` transports `R` to a sheaf of rings `R'` on `(C', J')`, and sheaves of
`R`-modules to sheaves of `R'`-modules, by an equivalence `Φ` of module categories
(`Stacks.SheafOfModules.reindexEquivalence`). Restriction along `e.functor` also identifies the
rings of global sections, `Γ(C, R) ≅ Γ(C', R')`, and the global sections of `M` with those of
`Φ M`. This file shows that the identification persists in every degree of cohomology:

`Hⁿ(C, M) ≅ Hⁿ(C', Φ M)`

as `Γ(C, R)`-modules, the right-hand side regarded as one by restriction of scalars along
`Γ(C, R) ⟶ Γ(C', R')`.

## Main definitions

* `Stacks.Cohomology.SiteModules.reindexGlobalSectionRingHom`: the ring map
  `Γ(C, R) ⟶ Γ(C', R')` restricting a global section along `e.functor`.
* `Stacks.Cohomology.SiteModules.reindexGlobalSectionsIso`: global sections of `M` are global
  sections of `Φ M`, naturally in `M`, as `Γ(C, R)`-modules.
* `Stacks.Cohomology.SiteModules.reindexGlobalModuleCohomologyIso`: **the comparison of
  cohomology** `Hⁿ(C, M) ≅ Hⁿ(C', Φ M)`.

## Main results

* `Stacks.Cohomology.SiteModules.bijective_reindexGlobalSectionRingHom`: the ring map of global
  sections is bijective.

## Implementation notes

The degree-zero identification is restriction along `e.functor.op`, which is bijective on
sections because an equivalence is initial (`CategoryTheory.Functor.bijective_sectionsPrecomp`).
In positive degree the comparison is the composite of three isomorphisms: the right derived
functors of the two isomorphic functors `Γ(C, -)` and `Φ ⋙ Γ(C', -) ⋙ res`, the collapse
`Rⁿ(Φ ⋙ T)(M) ≅ RⁿT(Φ M)` along the exact, injective-preserving functor `Φ`
(`Stacks.RightDerivedComp.objIso`), and the commutation of the exact functor of restriction of
scalars with right derived functors (`CategoryTheory.Functor.rightDerivedCompIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{r})

/-- The ring map `Γ(C, R) ⟶ Γ(C', R')` restricting a global section of `R` along the functor of
an equivalence of sites `e : C' ≌ C`, where `R'` is the transported sheaf of rings
`Stacks.SheafOfModules.reindexRing J' e R`. -/
def reindexGlobalSectionRingHom :
    GlobalSectionRing R →+* GlobalSectionRing (Stacks.SheafOfModules.reindexRing J' e R) where
  toFun s := ⟨fun X => s.1 (e.functor.op.obj X), fun f => s.2 (e.functor.op.map f)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [e.inverse.IsContinuous J J'] in
/-- The image of a global section `s` under `reindexGlobalSectionRingHom` has value
`s.1 (e.functor.op.obj X)` at an object `X` of `C'ᵒᵖ`. -/
@[simp]
theorem reindexGlobalSectionRingHom_apply_val (s : GlobalSectionRing R) (X : C'ᵒᵖ) :
    (reindexGlobalSectionRingHom J' e R s).1 X = s.1 (e.functor.op.obj X) :=
  rfl

omit [e.inverse.IsContinuous J J'] in
/-- **The ring map of global sections along an equivalence of sites is bijective**: an
equivalence is initial, so restriction along it is a bijection on sections. -/
theorem bijective_reindexGlobalSectionRingHom :
    Function.Bijective (reindexGlobalSectionRingHom J' e R) := by
  have h := Functor.bijective_sectionsPrecomp e.functor.op (R.obj ⋙ forget RingCat)
  refine ⟨fun s t hst => ?_, fun t => ?_⟩
  · have h' : e.functor.op.sectionsPrecomp (P := R.obj ⋙ forget RingCat) ⟨s.1, s.2⟩ =
        e.functor.op.sectionsPrecomp (P := R.obj ⋙ forget RingCat) ⟨t.1, t.2⟩ :=
      Subtype.ext (congrArg Subtype.val hst)
    exact Subtype.ext (congrArg Subtype.val (h.1 h'))
  · obtain ⟨s, hs⟩ := h.2 ⟨t.1, t.2⟩
    exact ⟨⟨s.1, s.2⟩, Subtype.ext (congrArg Subtype.val hs)⟩

/-- **Global sections are unchanged by transport along an equivalence of sites**: restriction
along `e.functor` identifies the global sections of a sheaf of `R`-modules `M` with those of its
transport `Φ M`, semilinearly along `Stacks.Cohomology.SiteModules.reindexGlobalSectionRingHom`,
naturally in `M`. -/
def reindexGlobalSectionsIso :
    globalSectionsFunctor.{u, v, r, w} R ≅
      (Stacks.SheafOfModules.reindexEquivalence.{r, w} (J' := J') e R).functor ⋙
        globalSectionsFunctor.{u, v, r, w} (Stacks.SheafOfModules.reindexRing J' e R) ⋙
        ModuleCat.restrictScalars (reindexGlobalSectionRingHom J' e R) :=
  NatIso.ofComponents
    (fun M => LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective
        ({ toFun := fun s => ⟨fun X => s.1 (e.functor.op.obj X), fun f => s.2 (e.functor.op.map f)⟩
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl } :
          (globalSectionsFunctor.{u, v, r, w} R).obj M →ₗ[GlobalSectionRing R]
            ((Stacks.SheafOfModules.reindexEquivalence.{r, w} (J' := J') e R).functor ⋙
              globalSectionsFunctor.{u, v, r, w} (Stacks.SheafOfModules.reindexRing J' e R) ⋙
              ModuleCat.restrictScalars (reindexGlobalSectionRingHom J' e R)).obj M)
        (by
          have h := Functor.bijective_sectionsPrecomp e.functor.op (M.val.presheaf ⋙ forget _)
          refine ⟨fun s t hst => h.1 (Subtype.ext (congrArg Subtype.val hst)), fun t => ?_⟩
          obtain ⟨s, hs⟩ := h.2 ⟨t.1, t.2⟩
          exact ⟨s, Subtype.ext (congrArg Subtype.val hs)⟩)))
    (fun _ => rfl)

/-- **The cohomology of modules is invariant under an equivalence of sites.** For a sheaf of
`R`-modules `M` and its transport `Φ M` along `e`, `Hⁿ(C, M) ≅ Hⁿ(C', Φ M)` as modules over
`Γ(C, R)`, the right-hand side regarded as one along
`Stacks.Cohomology.SiteModules.reindexGlobalSectionRingHom`. -/
def reindexGlobalModuleCohomologyIso (M : SheafOfModules.{max u v r w} R) (n : ℕ) :
    (globalModuleCohomology.{u, v, r, w} R n).obj M ≅
      (ModuleCat.restrictScalars (reindexGlobalSectionRingHom J' e R)).obj
        ((globalModuleCohomology.{u, v, r, w} (Stacks.SheafOfModules.reindexRing J' e R) n).obj
          ((Stacks.SheafOfModules.reindexEquivalence.{r, max u v r w} (J' := J') e R).functor.obj
            M)) := by
  let Φ := (Stacks.SheafOfModules.reindexEquivalence.{r, max u v r w} (J' := J') e R).functor
  let res := ModuleCat.restrictScalars.{max u v r w} (reindexGlobalSectionRingHom J' e R)
  let Γ' := globalSectionsFunctor.{u, v, r, max u v r w}
    (Stacks.SheafOfModules.reindexRing J' e R)
  have : Φ.IsEquivalence := inferInstance
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  have : PreservesFiniteLimits Φ := inferInstance
  have : PreservesFiniteColimits Φ := inferInstance
  have hres := ((Functor.exact_tfae res).out 2 4).mp fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢; assumption
  have : PreservesFiniteLimits res := hres.1
  have : PreservesFiniteColimits res := hres.2
  have : res.PreservesHomology := Functor.preservesHomologyOfExact res
  exact (Functor.rightDerivedIsoOfNatIso
      (reindexGlobalSectionsIso.{u, v, r, max u v r w} J' e R) n).app M ≪≫
    Stacks.RightDerivedComp.objIso Φ (injectiveResolution M)
      (Functor.isZero_rightDerived_of_exact Φ M) (Γ' ⋙ res) n ≪≫
    (Functor.rightDerivedCompIso Γ' res n).app (Φ.obj M)

/-- **Transport along an equivalence of sites commutes with raising the universe of the
sections**: both send `M` to the sheaf `X' ↦ ULift (M(e X'))`. -/
def reindexEquivalenceUliftForPresentationIso.{m, t} (M : SheafOfModules.{m} R) :
    (Stacks.SheafOfModules.reindexEquivalence.{r, max t m} (J' := J') e R).functor.obj
        (SheafOfModules.uliftForPresentation.{u, v, r, m, t} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, r, m, t}
        ((Stacks.SheafOfModules.reindexEquivalence.{r, m} (J' := J') e R).functor.obj M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))

end Stacks.Cohomology.SiteModules

end

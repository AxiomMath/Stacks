module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSites
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# Derived pullback of the sheafified base change from a terminal object

Let `(C, O)` be a ringed site with a terminal object `t` and put `R = O(t)`. The derived pullback
`Lp^* : D(R) ⥤ D(PMod O)` along the morphism of chaotic sites `(C, O) → (pt, R)`
(`Stacks.ModulesOnACategory.TerminalMorphismOfSites.Lpullback`, `M ↦ M ⊗^L_R O`) followed by
sheafification `ε^*` gives the functor

```
  tilde : D(R) ⥤ D(O),   M ↦ ε^*(M ⊗^L_R O),
```

the sheafified "tilde" of a complex of `R`-modules. This file computes its derived pullback along
a morphism of ringed sites. Let `f : (C, O) ⟶ (D, O')` be given by `u : D ⥤ C`, let `t` be a
terminal object of `D` such that `u(t)` is terminal in `C`, and let `φ : O'(t) → O(u t)` be the
structure map of `f` at `t`. Then

```
  Lf^*(tilde_D M) ≅ tilde_C (M ⊗^L_{O'(t)} O(u t)),
```

naturally in `M ∈ D(O'(t))`; when `φ` is an isomorphism (for instance when `O'` is the
restriction of `O` along `u`) the derived base change is restriction of scalars along `φ⁻¹`.

## Main results

* `Stacks.ModulesOnACategory.TildePullback.derivedPullbackTildeIso`:
  `Lf^* ∘ tilde_D ≅ tilde_C ∘ Lφ^*`.
* `Stacks.ModulesOnACategory.TildePullback.derivedPullbackTildeIsoOfIsIso`: the same with
  `Lφ^*` replaced by restriction of scalars along `φ⁻¹` when `φ` is an isomorphism.
* `Stacks.ModulesOnACategory.TildePullback.pullbackSheafifiedBaseChangeIso`: the underived
  statement.

## Implementation notes

Underived, the composite `f^* ∘ ε^* ∘ (- ⊗_{O'(t)} O')` is left adjoint to
`G ↦ G(u t)` read as an `O'(t)`-module through `φ`, and so is
`ε^* ∘ (- ⊗_{O(u t)} O) ∘ (- ⊗_{O'(t)} O(u t))`; uniqueness of adjoints identifies them
(`pullbackSheafifiedBaseChangeIso`). The right-hand side `tilde_C ∘ Lφ^*` is a total left derived
functor of the underived composite (`isLeftDerivedFunctor_extendScalarsTilde`), so the canonical
comparison of the left-hand side lifts to a natural transformation into it, and it remains to see
that this transformation is invertible. Every object of `D(O'(t))` is represented by a sequential
colimit `P` of bounded above complexes of projective modules
(`exists_quasiIso_colimit_isStrictlyLE_projective`). Such a `P` is K-flat, so both `Lp^*` and the
derived base change are computed on it degreewise; and the sheafified base change of `P` is again
a sequential colimit of bounded above complexes of flat `O'`-modules, hence K-flat with flat terms
(`kFlat_sheafifiedBaseChange_colimit`), so the derived pullback is computed on it degreewise as
well (Stacks 06YY). At `P` every comparison is therefore invertible.

No hypothesis on `u` beyond being a morphism of sites is needed, and the structure map need not be
an isomorphism.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.ModulesOnACategory.TildePullback

universe u

section Resolution

variable {R : Type u} [CommRing R]

/-- **A K-flat resolution presented as a colimit.** Every complex of modules over a commutative
ring receives a quasi-isomorphism from the colimit of a sequence of complexes `D n` which are
strictly bounded above (by `n`) and have projective terms. This is the resolution of Stacks 06Y4
with its colimit presentation exposed, which is what transports along a left adjoint. -/
theorem exists_quasiIso_colimit_isStrictlyLE_projective
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (α : colimit D ⟶ M),
      QuasiIso α ∧ (∀ n : ℕ, (D.obj n).IsStrictlyLE (n : ℤ)) ∧
        ∀ (n : ℕ) (i : ℤ), Projective ((D.obj n).X i) := by
  let P : ObjectProperty (ModuleCat.{u} R) := fun X => Projective X
  let : P.ContainsZero := ⟨ModuleCat.of R (Fin 0 → R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hsum : ∀ X Y : ModuleCat.{u} R, P X → P Y → P (X ⊞ Y) :=
    fun X Y (_ : Projective X) (_ : Projective Y) => (inferInstance : Projective (X ⊞ Y))
  have hcover : ∀ X : ModuleCat.{u} R, ∃ (Y : ModuleCat.{u} R) (_ : P Y) (p : Y ⟶ X), Epi p :=
    fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  obtain ⟨Q, q, g, hq, -, hle, hproj, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover M
  let D := Functor.ofSequence g
  let s : Cocone D := Cocone.mk M
    (NatTrans.ofSequence (fun n => q n ≫ M.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  refine ⟨D, colimit.desc D s, ?_, fun n => hle n, fun n i => hproj n i⟩
  let : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
  let : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  exact StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq
    (colimit.isColimit D) _ (fun n => colimit.ι_desc s n)

end Resolution

section Site

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The sections of the structure sheaf of a ringed site, as a presheaf of rings, commute. -/
instance commSections_ringSheaf (Z : RingedSite.{u, u, u}) :
    Stacks.TerminalBaseChange.CommSections (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj :=
  ⟨fun U x y => mul_comm (G := (Z.O.obj.obj U : Type u)) x y⟩

variable {Z : RingedSite.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {t : Z.C} (ht : IsTerminal t)

/-- **The sheafified base change of a flat module is flat.** For a flat `O(t)`-module `N` the
presheaf `U ↦ O(U) ⊗_{O(t)} N` has flat sections, so its sheafification is a flat `O`-module by
Stacks 0GN1. -/
theorem isFlat_epsilonPullback_baseChangePresheaf
    (N : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t)))
    [Module.Flat ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t)) N] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O)
      ((ChaoticComparison.epsilonPullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((TerminalBaseChange.baseChangePresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
          ht).obj N)) := by
  let a : Z.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj := 𝟙 _
  have : Presheaf.IsLocallyInjective Z.J a :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)
  have : Presheaf.IsLocallySurjective Z.J a :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)
  refine Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat
    Z.J (Osharp := Z.O) a _ (fun U => ?_)
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · exact Z.J.covering_of_eq_top
      (Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ PUnit.unit))
  · let := (TerminalBaseChange.rho (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj ht
      (op U)).toAlgebra
    exact (Module.Flat.baseChange ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t))
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op U))
      N :)

/-- **The sheafified base change** `N ↦ (N ⊗_{O(t)} O)^#` from modules over the sections over a
terminal object `t` to sheaves of `O`-modules. -/
abbrev sheafifiedBaseChange :
    ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t)) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) :=
  TerminalBaseChange.baseChangePresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj ht ⋙
    ChaoticComparison.epsilonPullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)

/-- The sheafified base change is left adjoint to taking sections over the terminal object. -/
def sheafifiedBaseChangeAdj :
    sheafifiedBaseChange ht ⊣
      ChaoticComparison.epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⋙
      PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj (op t) :=
  (TerminalBaseChange.baseChangeAdj.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj ht).comp
    (ChaoticComparison.epsilonAdjunction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- The sheafified base change is additive, being a left adjoint. -/
instance sheafifiedBaseChange_additive : (sheafifiedBaseChange ht).Additive :=
  (sheafifiedBaseChangeAdj ht).left_adjoint_additive

/-- **The sheafified base change of a sequential colimit of bounded above flat complexes is
K-flat with flat terms.** The sheafified base change is a left adjoint, so it commutes with the
colimit, and it carries each stage to a bounded above complex of flat `O`-modules
(`isFlat_epsilonPullback_baseChangePresheaf`), so Stacks 06YQ applies. -/
theorem kFlat_sheafifiedBaseChange_colimit
    (D : ℕ ⥤ CochainComplex
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t))) ℤ)
    (hLE : ∀ n : ℕ, (D.obj n).IsStrictlyLE (n : ℤ))
    (hflat : ∀ (n : ℕ) (i : ℤ),
      Module.Flat ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op t)) ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)
        (((sheafifiedBaseChange ht).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (colimit D)) ∧
      ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O)
        ((((sheafifiedBaseChange ht).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (colimit D)).X i) := by
  have : PreservesColimitsOfShape ℕ (sheafifiedBaseChange ht) :=
    (sheafifiedBaseChangeAdj ht).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (sheafifiedBaseChange ht)
  let e := preservesColimitIso ((sheafifiedBaseChange ht).mapHomologicalComplex
    (ComplexShape.up ℤ)) D
  let D' : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ :=
    D ⋙ (sheafifiedBaseChange ht).mapHomologicalComplex (ComplexShape.up ℤ)
  have hLE' : ∀ n : ℕ, ∃ b : ℤ, CochainComplex.IsStrictlyLE (D'.obj n) b := fun n => ⟨n, by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (sheafifiedBaseChange ht).map_isZero ((D.obj n).isZero_of_isStrictlyLE n i hi)⟩
  have hflat' : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Z.O) ((D'.obj n).X i) := fun n i => by
    have := hflat n i
    exact isFlat_epsilonPullback_baseChangePresheaf ht ((D.obj n).X i)
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat Z.O D'
      hLE' hflat'
  have hF := Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X Z.O D' hflat'
  exact ⟨CochainComplex.KFlatBifunctor.KFlat.of_iso _ hK e.symm, fun i =>
    AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Z.O
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso e.symm) (hF i)⟩

end Site

section Main

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 1500] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
  (isIso_derivedPullbackComparison_app_of_isKFlat)

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {t : Y.C} (ht : IsTerminal t) (hut : IsTerminal (f.u.obj t))

attribute [local instance] AlgebraicGeometry.RingedSite.derivedPullbackHasLeftDerived

/-- The inverse image of sheaves of modules along `f` is additive, being a left adjoint. -/
local instance additive_pullbackTopos' : f.toRingedToposSiteHom.pullbackTopos.Additive :=
  have := RingedToposSiteHom.pushforwardTopos_additive.{u} f.toRingedToposSiteHom
  Adjunction.left_adjoint_additive
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f.toRingedToposSiteHom)

/-- The structure map `O_D(t) ⟶ O_C(u t)` of a morphism of ringed sites at an object `t`. -/
abbrev structureMapAt (t : Y.C) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op t) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (f.u.obj t)) :=
  f.toRingedToposSiteHom.fSharpRing.hom.app (op t)

/-- The structure map at `t`, as a ring homomorphism `O_D(t) →+* O_C(u t)`. -/
abbrev structureRingHomAt (t : Y.C) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op t) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (f.u.obj t)) :=
  (structureMapAt f t).hom

/-- Sections over `t` of the direct image of a sheaf of modules `G` along `f` are the sections of
`G` over `u(t)`, regarded as an `O_D(t)`-module through the structure map. The two sides agree on
the nose. -/
def pushforwardSectionsIso :
    f.toRingedToposSiteHom.pushforwardTopos ⋙
        (ChaoticComparison.epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
          PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
            (op t)) ≅
      (ChaoticComparison.epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
          (op (f.u.obj t))) ⋙
          ModuleCat.restrictScalars.{u} (structureRingHomAt f t) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The underived computation.** Pulling back the sheafified base change from a terminal object
`t` along `f` is the sheafified base change from `u(t)` after extension of scalars along the
structure map: both are left adjoint to `G ↦ G(u t)` read through the structure map
(`pushforwardSectionsIso`). -/
def pullbackSheafifiedBaseChangeIso :
    sheafifiedBaseChange ht ⋙ f.toRingedToposSiteHom.pullbackTopos ≅
      ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙ sheafifiedBaseChange hut :=
  ((sheafifiedBaseChangeAdj ht).comp
      f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (structureRingHomAt f t)).comp
      (sheafifiedBaseChangeAdj hut)).ofNatIsoRight (pushforwardSectionsIso f).symm)

/-- **The derived tilde functor** `M ↦ ε^*(M ⊗^L_{O(s)} O)` on a ringed site with a terminal
object `s`: the derived pullback of
`Stacks.ModulesOnACategory.TerminalMorphismOfSites.Lpullback` followed by sheafification. -/
abbrev tilde {Z : RingedSite.{u, u, u}}
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {s : Z.C} (hs : IsTerminal s) :
    DerivedCategory (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op s))) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  TerminalMorphismOfSites.Lpullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs ⋙
    (ChaoticComparison.epsilonPullback.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).mapDerivedCategory

/-- The comparison exhibiting `tilde` as the total left derived functor of the sheafified base
change. -/
abbrev tildeComparison {Z : RingedSite.{u, u, u}}
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {s : Z.C} (hs : IsTerminal s) :
    DerivedCategory.Q ⋙ tilde hs ⟶
      (sheafifiedBaseChange hs).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  CochainComplex.KFlatAdjunction.postcompComparison
    (TerminalBaseChange.baseChangePresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (ChaoticComparison.epsilonPullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (TerminalMorphismOfSites.Lpullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.LpullbackComparison.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)

/-- `tilde` is a total left derived functor of the sheafified base change. -/
instance isLeftDerivedFunctor_tilde {Z : RingedSite.{u, u, u}}
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {s : Z.C} (hs : IsTerminal s) :
    (tilde hs).IsLeftDerivedFunctor (tildeComparison hs)
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcompMapDerivedCategory
    (TerminalBaseChange.baseChangePresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.quasiIso_baseChangePresheaf_map.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (ChaoticComparison.epsilonPullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (TerminalMorphismOfSites.Lpullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.LpullbackComparison.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)

/-- `tilde` is computed degreewise on a K-flat complex. -/
theorem isIso_tildeComparison_app {Z : RingedSite.{u, u, u}}
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {s : Z.C} (hs : IsTerminal s)
    (P : CochainComplex
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op s))) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    IsIso ((tildeComparison hs).app P) := by
  have := CochainComplex.KFlatAdjunction.isIso_app_of_kFlat
    (TerminalBaseChange.baseChangePresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.quasiIso_baseChangePresheaf_map.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.Lpullback.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs)
    (TerminalMorphismOfSites.LpullbackComparison.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj hs) P hP
  rw [CochainComplex.KFlatAdjunction.postcompComparison_app]
  infer_instance

/-- The canonical comparison `Lf^* ⟶ f^*` of Stacks 06YY, read on cochain complexes through
the localization functor `DerivedCategory.Q`. -/
def derivedPullbackComparisonQ :
    DerivedCategory.Q ⋙ derivedPullback.{u} f.toRingedToposSiteHom ⟶
      f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (derivedPullback.{u} f.toRingedToposSiteHom) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (derivedPullbackComparison.{u} f.toRingedToposSiteHom) ≫
    Functor.whiskerRight (f.toRingedToposSiteHom.pullbackTopos.mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)) (DerivedCategory.quotientCompQhIso _).hom

/-- The comparison `Lf^* ⟶ f^*` is invertible at a K-flat complex with flat terms
(Stacks 06YY). -/
theorem isIso_derivedPullbackComparisonQ_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hKX : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso ((derivedPullbackComparisonQ f).app K) := by
  have := isIso_derivedPullbackComparison_app_of_isKFlat f.toRingedToposSiteHom
    f.isMorphismOfSites ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ⟨hK, hKX⟩
  dsimp only [derivedPullbackComparisonQ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- Extension of scalars is additive, being a left adjoint. -/
local instance extendScalarsAt_additive :
    (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (structureRingHomAt f t)).left_adjoint_additive

/-- Derived extension of scalars `- ⊗^L_{O_D(t)} O_C(u t)` along the structure map at `t`. -/
abbrev derivedExtendScalarsAt :
    DerivedCategory (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op t))) ⥤
      DerivedCategory
        (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (f.u.obj t)))) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (structureRingHomAt f t)).functor

/-- The comparison exhibiting `tilde_C ∘ Lφ^*` as a total left derived functor of the composite
of extension of scalars along the structure map and the sheafified base change. -/
def extendScalarsTildeComparison :
    DerivedCategory.Q ⋙ (derivedExtendScalarsAt f (t := t) ⋙ tilde hut) ⟶
      (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙
        sheafifiedBaseChange hut).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (structureRingHomAt f t)).comparison (tilde hut) ≫
    Functor.whiskerLeft ((ModuleCat.extendScalars.{u, u, u}
      (structureRingHomAt f t)).mapHomologicalComplex (ComplexShape.up ℤ)) (tildeComparison hut) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙
        sheafifiedBaseChange hut)) (ComplexShape.up ℤ)).hom DerivedCategory.Q

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The comparison of `tilde_C ∘ Lφ^*` is invertible on K-flat complexes: derived extension of
scalars is computed degreewise there, and it carries K-flat complexes to K-flat complexes
(Stacks 06Y1). -/
theorem isIso_extendScalarsTildeComparison_app
    (P : CochainComplex
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op t))) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    IsIso ((extendScalarsTildeComparison f hut).app P) := by
  have := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (structureRingHomAt f t)).comparison_isIso_of_kFlat P hP
  have := isIso_tildeComparison_app hut _
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u}
      (structureRingHomAt f t) P hP)
  refine IsIso.comp_isIso' (Functor.map_isIso (tilde hut) _) ?_
  refine IsIso.comp_isIso' this ?_
  exact IsIso.comp_isIso' inferInstance
    (Functor.map_isIso DerivedCategory.Q (((Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙
        sheafifiedBaseChange hut)) (ComplexShape.up ℤ)).app P).hom))

/-- `tilde_C ∘ Lφ^*` is a total left derived functor of extension of scalars along the
structure map followed by the sheafified base change. -/
instance isLeftDerivedFunctor_extendScalarsTilde :
    (derivedExtendScalarsAt f (t := t) ⋙ tilde hut).IsLeftDerivedFunctor
      (extendScalarsTildeComparison f hut)
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
  CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat _ _
    (CochainComplex.KFlatAdjunction.quotientCompMapIso
      (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙ sheafifiedBaseChange hut))
    _ _ (isIso_extendScalarsTildeComparison_app f hut)

/-- The canonical comparison of `Lf^* ∘ tilde_D` with the underived composite: the comparison of
`tilde_D`, the comparison `Lf^* ⟶ f^*`, and the underived computation
`pullbackSheafifiedBaseChangeIso`. -/
def tildeDerivedPullbackComparison :
    DerivedCategory.Q ⋙ (tilde ht ⋙ derivedPullback.{u} f.toRingedToposSiteHom) ⟶
      (ModuleCat.extendScalars.{u, u, u} (structureRingHomAt f t) ⋙
        sheafifiedBaseChange hut).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (tildeComparison ht) (derivedPullback.{u} f.toRingedToposSiteHom) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((sheafifiedBaseChange ht).mapHomologicalComplex (ComplexShape.up ℤ))
      (derivedPullbackComparisonQ f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (pullbackSheafifiedBaseChangeIso f ht hut) (ComplexShape.up ℤ)).hom DerivedCategory.Q

/-- **The derived pullback of the sheafified tilde.** For a morphism of ringed sites
`f : (C, O) ⟶ (D, O')` given by `u`, a terminal object `t` of `D` with `u(t)` terminal in `C`,
and `M` in `D(O'(t))`,

`Lf^*(ε^*(M ⊗^L_{O'(t)} O')) ≅ ε^*((M ⊗^L_{O'(t)} O(u t)) ⊗^L_{O(u t)} O)`,

naturally in `M`. The isomorphism is the lift of the canonical comparison
(`tildeDerivedPullbackComparison`) through the left derived universal property of the right-hand
side; it is invertible because every object is represented by a sequential colimit of bounded
above complexes of projective modules, on which every comparison involved is invertible. -/
def derivedPullbackTildeIso :
    tilde ht ⋙ derivedPullback.{u} f.toRingedToposSiteHom ≅
      derivedExtendScalarsAt f (t := t) ⋙ tilde hut :=
  have : IsIso ((derivedExtendScalarsAt f (t := t) ⋙ tilde hut).leftDerivedLift
      (extendScalarsTildeComparison f hut) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (tildeDerivedPullbackComparison f ht hut)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    obtain ⟨D, α, hα, hLE, hproj⟩ :=
      exists_quasiIso_colimit_isStrictlyLE_projective (DerivedCategory.Q.objPreimage K)
    have hQα : IsIso (DerivedCategory.Q.map α) := by
      rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
    let eK : DerivedCategory.Q.obj (colimit D) ≅ K :=
      asIso (DerivedCategory.Q.map α) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    rw [← NatTrans.isIso_app_iff_of_iso _ eK]
    have hflat : ∀ (n : ℕ) (i : ℤ),
        Module.Flat ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op t)) ((D.obj n).X i) :=
      fun n i => have := hproj n i; inferInstance
    have hK : CochainComplex.KFlat.{u, u} (colimit D) :=
      CochainComplex.KFlat.kFlat_colimit D (fun n => by
        have := hLE n
        have := hflat n
        exact CochainComplex.KFlat.kFlat_of_flat (D.obj n) n)
    have hR := isIso_extendScalarsTildeComparison_app f hut _ hK
    have hL : IsIso ((tildeDerivedPullbackComparison f ht hut).app (colimit D)) := by
      obtain ⟨hK₁, hK₂⟩ := kFlat_sheafifiedBaseChange_colimit ht D hLE hflat
      have h₁ := isIso_tildeComparison_app ht _ hK
      have h₂ := isIso_derivedPullbackComparisonQ_app f _ hK₁ hK₂
      refine IsIso.comp_isIso' inferInstance ?_
      refine IsIso.comp_isIso' (Functor.map_isIso (derivedPullback.{u} f.toRingedToposSiteHom)
        ((tildeComparison ht).app (colimit D))) ?_
      refine IsIso.comp_isIso' inferInstance ?_
      refine IsIso.comp_isIso' h₂ ?_
      exact IsIso.comp_isIso' inferInstance
        (Functor.map_isIso DerivedCategory.Q (((Functor.mapHomologicalComplexCompIso
          (pullbackSheafifiedBaseChangeIso f ht hut) (ComplexShape.up ℤ)).app (colimit D)).hom))
    have hfac := (derivedExtendScalarsAt f (t := t) ⋙ tilde hut).leftDerived_fac_app
      (extendScalarsTildeComparison f hut) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (tildeDerivedPullbackComparison f ht hut) (colimit D)
    rw [← hfac] at hL
    exact IsIso.of_isIso_comp_right _ ((extendScalarsTildeComparison f hut).app (colimit D))
  asIso ((derivedExtendScalarsAt f (t := t) ⋙ tilde hut).leftDerivedLift
      (extendScalarsTildeComparison f hut) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (tildeDerivedPullbackComparison f ht hut))

/-- Derived extension of scalars along a ring isomorphism is restriction of scalars along its
inverse: both are total left derived functors of extension of scalars, and underived they agree
(`ModuleCat.extendScalarsIsoRestrictScalarsSymm`). -/
def derivedExtendScalarsAtIsoOfIsIso [IsIso (structureMapAt f t)] :
    derivedExtendScalarsAt f (t := t) ≅
      (ModuleCat.restrictScalars.{u} (inv (structureMapAt f t)).hom).mapDerivedCategory :=
  letI := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (ModuleCat.restrictScalars.{u} (inv (structureMapAt f t)).hom).mapDerivedCategory
    (ModuleCat.restrictScalars.{u} (inv (structureMapAt f t)).hom).mapDerivedCategoryFactors
  Functor.leftDerivedNatIso _ _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (structureRingHomAt f t)).comparison
    (ModuleCat.restrictScalars.{u} (inv (structureMapAt f t)).hom).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsIsoRestrictScalarsSymm
        (asIso (structureMapAt f t)).ringCatIsoToRingEquiv) (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- **The derived pullback of the sheafified tilde, when the structure map at `t` is an
isomorphism.** In that case (for instance when the structure sheaf of the target is the
restriction of that of the source), `Lf^*(ε^*(M ⊗^L_{O'(t)} O')) ≅ ε^*(M ⊗^L_{O(u t)} O)`,
naturally in `M`, where `M` is regarded as an `O(u t)`-module through the inverse of the
structure map. -/
def derivedPullbackTildeIsoOfIsIso [IsIso (structureMapAt f t)] :
    tilde ht ⋙ derivedPullback.{u} f.toRingedToposSiteHom ≅
      (ModuleCat.restrictScalars.{u} (inv (structureMapAt f t)).hom).mapDerivedCategory ⋙
        tilde hut :=
  derivedPullbackTildeIso f ht hut ≪≫
    Functor.isoWhiskerRight (derivedExtendScalarsAtIsoOfIsIso f) (tilde hut)

end Main

end Stacks.ModulesOnACategory.TildePullback

end

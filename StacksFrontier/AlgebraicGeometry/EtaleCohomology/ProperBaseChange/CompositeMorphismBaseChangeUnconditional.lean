module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliaryUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Triangulated.DimensionShifting

/-!
# CompositeMorphismBaseChangeUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built on
them.

## Main results

* `CohomologyCommutesWithBaseChange.comp`: cohomology commutes with base change for a composite
  of proper morphisms for which it commutes with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section DirectImageCompIso

variable {X Y Z : Scheme.{u}}

end DirectImageCompIso

section Whisker

end Whisker

section CompositeSquare

variable {X Y Z X' Y' Z' : Scheme.{u}}

end CompositeSquare

section Main

variable {X Y Z X' Y' Z' : Scheme.{u}}

end Main

section Acyclic

variable {X Y : Scheme.{u}}

/-- **An abelian sheaf without higher direct images is its own derived direct image.**  If
`H^q(Rh_* F) = 0` for every `q > 0`, then `Rh_* F` is the sheaf `h_* F` placed in degree zero.

`Rh_* F` has no cohomology in negative degrees by left t-exactness of the unbounded derived
direct image, so the vanishing concentrates it in degree zero, where its cohomology is
`R⁰h_* F = h_* F`. -/
public theorem nonempty_singleFunctor_iso_etaleAbelianDerivedDirectImage (h : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} h).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)))) :
    Nonempty ((DerivedCategory.singleFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
          ((etaleAbelianDirectImage.{u, v} h).obj F) ≅
      (etaleAbelianDerivedDirectImage.{u, v} h).obj
        ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)) := by
  set K := (etaleAbelianDerivedDirectImage.{u, v} h).obj
    ((DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)
  have : K.IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (etaleAbelianDirectImage.{u, v} h) _ 0
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i hi => hF i hi
  obtain ⟨Y₀, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  have : PreservesFiniteLimits (etaleAbelianDirectImage.{u, v} h) := by
    have : PreservesLimitsOfSize.{0, 0} (etaleAbelianDirectImage.{u, v} h) :=
      (etaleAbelianInverseImageDirectImageAdj.{u, v} h).rightAdjoint_preservesLimits
    infer_instance
  let e₀ : Y₀ ≅ (etaleAbelianDirectImage.{u, v} h).obj F :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y₀).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
      Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso
        (etaleAbelianDirectImage.{u, v} h) (etaleAbelianDerivedDirectImage.{u, v} h)
        (etaleAbelianDerivedDirectImageUnit.{u, v} h)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective F 0
  exact ⟨(DerivedCategory.singleFunctor _ 0).mapIso e₀.symm ≪≫ e.symm⟩

end Acyclic

section Condition

variable {X Y Z : Scheme.{u}}

/-- **The composition step of Stacks 0A4D at one torsion sheaf.**  Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms for which cohomology commutes with base change, let
```
X' --e--> X
|q        |f ≫ g
v         v
Z' --c--> Z
```
be cartesian, and let `F` be a torsion abelian sheaf on `X_étale` whose derived direct image
`Rf_* F` is a torsion abelian sheaf `G` on `Y_étale` placed in degree zero.  Then the base change
map `c⁻¹ R(gf)_* F ⟶ Rq_* e⁻¹ F` of the square is an isomorphism.

The square is factored through `Y' = Y ×_Z Z'`; the upper square is cartesian by the pasting
law, so the condition for `f` applies to it at `F`, and the condition for `g` applies to the
lower square at `G`, hence, by naturality, at `Rf_* F ≅ G[0]`.  The composition formula
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_compDirectImage_app` assembles the two. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_comp_of_iso_single
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hg : CohomologyCommutesWithBaseChange.{u, v} g)
    {X' Z' : Scheme.{u}} (c : Z' ⟶ Z) (e : X' ⟶ X) (q : X' ⟶ Z')
    (sq : IsPullback e q (f ≫ g) c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G)
    (φ : (DerivedCategory.singleFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G ≅
      (etaleAbelianDerivedDirectImage.{u, v} f).obj
        ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} (f ≫ g) c e q sq.w F) := by
  let t := IsPullback.of_hasPullback g c
  let f' : X' ⟶ pullback g c := t.lift (e ≫ f) q (by rw [Category.assoc, sq.w])
  have s₂ : IsPullback e f' f (pullback.fst g c) := IsPullback.of_bot' sq t
  have hq : q = f' ≫ pullback.snd g c := (t.lift_snd _ _ _).symm
  have h₂ := hf (pullback.fst g c) e f' s₂ F hF
  have h₁ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} g c (pullback.fst g c)
      (pullback.snd g c) t.w).app ((etaleAbelianDerivedDirectImage.{u, v} f).obj
        ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F))) :=
    (NatTrans.isIso_app_iff_of_iso _ φ).mp (hg c (pullback.fst g c) (pullback.snd g c) t G hG)
  unfold etaleAbelianSheafDerivedBaseChange at h₂ ⊢
  rw [etaleAbelianDerivedBaseChange_compDirectImage_app.{u, v} f g (f ≫ g) rfl c
    (pullback.fst g c) (pullback.snd g c) e f' q hq t.w s₂.w sq.w]
  infer_instance

end Condition

section Injective

open Stacks.Cohomology.ZModSheaf

variable {X Y Z : Scheme.{u}}

/-- **The direct image of the underlying abelian sheaf of a sheaf of `ℤ/ℓℤ`-modules is
torsion**, for `ℓ > 0`: its sections are sections of that sheaf over an étale base change, hence
annihilated by `ℓ`. -/
public theorem torsionSheafProperty_etaleAbelianDirectImage_toSheaf_zmod (h : X ⟶ Y) {ℓ : ℕ}
    (hℓ : 0 < ℓ)
    (M : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology ℓ)) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((etaleAbelianDirectImage.{u, v} h).obj ((SheafOfModules.toSheaf _).obj M)) := fun U _ ↦
  ⟨⊤, Y.smallEtaleTopology.top_mem U, fun _ _ _ ↦
    ⟨ℓ, hℓ, nsmul_toSheaf_eq_zero.{max (u + 1) v, max (u + 1) v} _ ℓ M _ _⟩⟩

/-- **The base change map of a composite is invertible at an injective sheaf of
`ℤ/nℤ`-modules**, `n > 0`, as soon as cohomology commutes with base change for the two factors.
This is the argument of Stacks 0A4D.  The underlying abelian sheaf `J` of the injective sheaf is
torsion and acyclic for every direct image (Tag 03FD), so `Rf_* J = (f_* J)[0]`, a torsion sheaf
placed in degree zero, and
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_comp_of_iso_single` applies.
No properness is used. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_comp_toSheaf_injective
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hg : CohomologyCommutesWithBaseChange.{u, v} g)
    {X' Z' : Scheme.{u}} (c : Z' ⟶ Z) (e : X' ⟶ X) (q : X' ⟶ Z')
    (sq : IsPullback e q (f ≫ g) c) {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) [Injective J] :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} (f ≫ g) c e q sq.w
      ((SheafOfModules.toSheaf _).obj J)) := by
  obtain ⟨φ⟩ := nonempty_singleFunctor_iso_etaleAbelianDerivedDirectImage.{u, v} f
    ((SheafOfModules.toSheaf _).obj J)
    (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, v} f n J)
  exact isIso_etaleAbelianSheafDerivedBaseChange_comp_of_iso_single.{u, v} f g hf hg c e q sq
    _ (torsionSheafProperty_toSheaf_zmod hn J) _
    (torsionSheafProperty_etaleAbelianDirectImage_toSheaf_zmod.{u, v} f hn J) φ

/-- **The base change map of a composite is invertible at every sheaf killed by a positive
integer `n`**, as soon as cohomology commutes with base change for the two factors.  The sheaves
on `X_étale` killed by `n`, placed in degree zero, form a class to which dimension shifting
(`Stacks.Triangulated.isIso_app_of_dimensionShifting`) applies: each embeds in the underlying
sheaf of an injective sheaf of `ℤ/nℤ`-modules
(`Stacks.EtaleCohomology.exists_mono_toSheaf_injective_univ`), at which the base change map is
invertible (`isIso_etaleAbelianSheafDerivedBaseChange_comp_toSheaf_injective`), with a cokernel
again killed by `n`; and both sides vanish in negative degrees. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_comp_of_nsmul_id_eq_zero
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hg : CohomologyCommutesWithBaseChange.{u, v} g)
    {X' Z' : Scheme.{u}} (c : Z' ⟶ Z) (e : X' ⟶ X) (q : X' ⟶ Z')
    (sq : IsPullback e q (f ≫ g) c) (n : ℕ) (hn : 0 < n)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hA : n • 𝟙 A = 0) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} (f ≫ g) c e q sq.w A) := by
  refine Stacks.Triangulated.isIso_app_of_dimensionShifting
    (etaleAbelianDerivedBaseChange.{u, v} (f ≫ g) c e q sq.w)
    (fun K ↦ ∃ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      n • 𝟙 A = 0 ∧ K = (DerivedCategory.singleFunctor _ 0).obj A) ?_ ?_ _ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨J, hJ, i, hi⟩ := exists_mono_toSheaf_injective_univ.{u, v} n A hA
    have hS := ShortComplex.ShortExact.mk' (S := ShortComplex.mk i (cokernel.π i)
      (cokernel.condition i)) (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
      hi inferInstance
    refine ⟨_, _, _, _, _, hS.singleTriangle_distinguished, ?_, cokernel i, ?_, rfl⟩
    · have := hJ
      exact isIso_etaleAbelianSheafDerivedBaseChange_comp_toSheaf_injective.{u, v} f g hf hg c e
        q sq hn J
    · exact Stacks.ConstantSheaf.nsmul_id_zero_of_epi (cokernel.π i) n
        (nsmul_id_toSheaf_eq_zero.{u, v} n J)
  · rintro _ ⟨A, -, rfl⟩ p hp
    exact isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg.{u, v} (f ≫ g) c e q sq.w
      A p hp

end Injective

section Main

variable {X Y Z : Scheme.{u}}

/-- **[Stacks, Tag 0A4D]: cohomology commutes with base change for a composite.**  Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be proper morphisms of schemes.  Assume

1. cohomology commutes with base change for `f`, and
2. cohomology commutes with base change for `g`.

Then cohomology commutes with base change for `g ∘ f`.

Cohomology commuting with base change is
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange`: the derived base change map
`c⁻¹ R(gf)_* F ⟶ Rq_* e⁻¹ F` is an isomorphism for every cartesian square over `g ∘ f` and every
torsion abelian sheaf `F` on `X_étale`, in all degrees at once.  The proof follows the source: at
an injective sheaf of `ℤ/nℤ`-modules the composition formula for base change maps reduces the
statement to the conditions for `f` and `g`
(`isIso_etaleAbelianSheafDerivedBaseChange_comp_toSheaf_injective`); dimension shifting carries
it to every sheaf killed by `n`, which is how the source uses Tag 0A4B; and a torsion sheaf is
the filtered colimit of its subsheaves killed by an integer, with which both sides commute as
`g ∘ f` is quasi-compact and quasi-separated (Tag 09Z1). -/
@[stacks 0A4D]
public theorem CohomologyCommutesWithBaseChange.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsProper f] [IsProper g]
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hg : CohomologyCommutesWithBaseChange.{u, v} g) :
    CohomologyCommutesWithBaseChange.{u, v} (f ≫ g) := by
  intro _ _ c e q sq
  exact isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_isPullback (f ≫ g) c e q
    sq (isIso_etaleAbelianSheafDerivedBaseChange_comp_of_nsmul_id_eq_zero.{u, v} f g hf hg c e q sq)

end Main

end Stacks.EtaleCohomology

end

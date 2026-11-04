module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces along an exact functor on derived categories

Let `Φ : Mod_R ⥤ Mod_S` be an exact functor carrying finite projective modules to finite
projective modules and `θ : Φ ⟶ Φ` a natural endomorphism. For a perfect complex `K` of
`R`-modules with an endomorphism `a`, the complex `Φ(K)` is perfect and

`Tr_S(θ_K ∘ Φ(a) | Φ(K)) = Φ♮(Tr_R(a | K))`,

where `Φ(K)` and `θ_K` are the degreewise actions of `Φ` and `θ` on the derived category. This is
`CategoryTheory.FilteredDerived.perfectDerivedTrace_functor` read in the derived category: both
sides are computed on a bounded complex of finite projective modules representing `K`.

The application is to restriction of scalars along `Λ → Λ[G]` twisted by the action of a group
element (`Stacks.Trace.conjugacyTrace`), in Steps 7 and 8 of the proof of [Stacks, Tag 03UG].

## Main results

* `CategoryTheory.FilteredDerived.isPerfect_mapDerivedCategory_of_preservesFiniteProjective`
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_mapDerivedCategory`
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_mapDerivedCategoryPlus`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' w

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{w} S) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (θ : Φ ⟶ Φ)
  (hΦ : PreservesFiniteProjective.{u, v} Φ)

include hΦ in
/-- **An exact functor preserving finite projective modules preserves perfect complexes.** -/
@[sga "6 I 4.18" "One-point site case"]
theorem isPerfect_mapDerivedCategory_of_preservesFiniteProjective
    {X : DerivedCategory (ModuleCat.{max u v} R)} (hX : StacksDraft.Perfect.IsPerfect X) :
    StacksDraft.Perfect.IsPerfect (Φ.mapDerivedCategory.obj X) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R X).mp hX
  exact (isPerfect_iff S _).mpr ⟨_, finiteProjectiveComplex_map Φ hΦ P hP,
    ⟨(Φ.mapDerivedCategoryFactors.app P).symm ≪≫ Φ.mapDerivedCategory.mapIso e⟩⟩

/-- **Functoriality of the trace along an exact functor, in the derived category.** For a perfect
complex `X` of `R`-modules with an endomorphism `a`,
`Tr_S(θ_X ∘ Φ(a) | Φ(X)) = Φ♮(Tr_R(a | X))`. -/
theorem perfectDerivedTrace_mapDerivedCategory (X : PerfectDerivedCategory.{u, max u v} R)
    (a : X.obj ⟶ X.obj) (hX' : StacksDraft.Perfect.IsPerfect (Φ.mapDerivedCategory.obj X.obj)) :
    perfectDerivedTrace S ⟨_, hX'⟩
        ((Stacks.DerivedFunctor.mapDerivedNatTrans θ).app X.obj ≫ Φ.mapDerivedCategory.map a) =
      functorTraceMap Φ θ hΦ (perfectDerivedTrace R X a) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R X.obj).mp X.property
  let : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    let : P.IsStrictlyLE d := hd
    let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
    let (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  obtain ⟨gh, hgh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj P)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).hom.app P ≫
        (e.hom ≫ a ≫ e.inv) ≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective gh
  have hg : DerivedCategory.Q.map g = e.hom ≫ a ≫ e.inv := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).hom.app P),
      ← DerivedCategory.quotientCompQhIso_hom_naturality, hgh]
    simp
  let e' : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      Φ.mapDerivedCategory.obj X.obj :=
    (Φ.mapDerivedCategoryFactors.app P).symm ≪≫ Φ.mapDerivedCategory.mapIso e
  refine perfectDerivedTrace_functor Φ θ hΦ X a P hP e g hg ⟨_, hX'⟩ _ e' ?_
  have hθ := Stacks.DerivedFunctor.mapDerivedNatTrans_factors_app θ P
  have hn := Φ.mapDerivedCategoryFactors.hom.naturality g
  have hθe := (Stacks.DerivedFunctor.mapDerivedNatTrans θ).naturality e.hom
  simp only [Functor.comp_map] at hn
  simp only [e', Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hθe, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc e.hom,
    ← hg, hn, reassoc_of% hθ, Iso.inv_hom_id_app_assoc]

/-- **Functoriality of the trace along an exact functor, on bounded below derived categories.**
For `K` with `ι(K)` perfect and an endomorphism `a`,
`Tr_S(θ_K ∘ Φ(a) | Φ(K)) = Φ♮(Tr_R(a | K))`. -/
theorem perfectDerivedTrace_mapDerivedCategoryPlus
    (K : DerivedCategory.Plus (ModuleCat.{max u v} R))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj K)) (a : K ⟶ K)
    (hK' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (Φ.mapDerivedCategoryPlus.obj K))) :
    perfectDerivedTrace S ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map
        ((Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θ).app K ≫
          Φ.mapDerivedCategoryPlus.map a)) =
      functorTraceMap Φ θ hΦ (perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map a)) :=
  perfectDerivedTrace_mapDerivedCategory Φ θ hΦ ⟨_, hK⟩ (DerivedCategory.Plus.ι.map a) hK'

end CategoryTheory.FilteredDerived

end

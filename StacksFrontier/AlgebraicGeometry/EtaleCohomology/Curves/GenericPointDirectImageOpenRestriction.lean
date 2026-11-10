module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# The cohomology of `j_* 𝐆_{m,η}` restricted to an open of a smooth curve

Let `X` be a smooth curve over an algebraically closed field `k`, let `j : η = Spec k(X) ⟶ X` be
the inclusion of the generic point and let `U ⊆ X` be a nonempty open subscheme. Then

`H^p_étale(U, (j_* 𝐆_{m,η})|_U) = 0` for every `p ≥ 1`.

For `U = X` this is Stacks 03RK. The proof is the same edge argument. Since `R^q j_* 𝐆_{m,η} = 0`
for `q ≥ 1` (Stacks 03RJ), `j_*` carries an injective resolution of `𝐆_{m,η}` to an injective
resolution of `j_* 𝐆_{m,η}`, and restriction to `U` keeps it an injective resolution (it is exact
and preserves injectives). So the cohomology in question is that of
`Γ(U, -) ∘ (-)|_U ∘ j_*` on an injective resolution of `𝐆_{m,η}`. That functor is `Γ(η, -)`:
the generic point lies in `U`, so `U ×_X η → η` is an isomorphism and is a final object of the
small étale site of `η`. Hence the cohomology is `H^p(η, 𝐆_m)`, zero by Stacks 03RG.

This is the vanishing that makes the restriction to `U` of the divisor sequence of Stacks 03RI
compute `H¹(U, 𝐆_m)` as a quotient of the global sections of `⨁_x i_{x,*} 𝐙` over `U`.

## Main results

* `Stacks.EtaleCohomology.isTerminal_smallEtaleBaseChange_smallEtaleCompose_terminal`: the
  generic fibre of an open containing the generic point is a final object of `η_étale`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_etaleRestriction_genericPointDirectImage`:
  **the vanishing above**.

## References

* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ)
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- If `j : Y ⟶ X` factors through a monomorphism `m : U ⟶ X`, the second projection of the
fibre product of `m` and `j` is an isomorphism. -/
theorem isIso_pullback_snd_of_factors {C : Type*} [Category C] {U X Y : C} (m : U ⟶ X) [Mono m]
    (j : Y ⟶ X) (h : Y ⟶ U) (hh : h ≫ m = j) [HasPullback m j] :
    IsIso (pullback.snd m j) := by
  refine ⟨pullback.lift h (𝟙 Y) (by rw [hh, Category.id_comp]), ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
    apply (cancel_mono m).1
    rw [Category.assoc, hh, pullback.condition]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U]

/-- **The inclusion of the generic point factors through every nonempty open.** -/
theorem range_genericPointInclusion_subset (U : X.Opens) [Nonempty U] :
    Set.range (genericPointInclusion X).base ⊆ Set.range U.ι.base := by
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  rw [genericPointInclusion_closedPoint, Scheme.Opens.range_ι]
  obtain ⟨x⟩ := ‹Nonempty U›
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x.1, trivial, x.2⟩

/-- **The generic fibre of a nonempty open is a final object of `η_étale`**: the base change to
`η` of the final object of `U_étale`, viewed over `X`, has as structure morphism the projection
`U ×_X η → η`, an isomorphism because `η ⟶ X` factors through the open immersion `U ⟶ X`. -/
def isTerminal_smallEtaleBaseChange_smallEtaleCompose_terminal :
    IsTerminal ((smallEtaleBaseChange (genericPointInclusion X)).obj
      ((Scheme.Etale.smallEtaleCompose U.ι).obj (Scheme.Etale.mk (𝟙 (U : Scheme.{u}))))) := by
  have : IsIso ((smallEtaleBaseChange (genericPointInclusion X)).obj
      ((Scheme.Etale.smallEtaleCompose U.ι).obj (Scheme.Etale.mk (𝟙 (U : Scheme.{u}))))).hom := by
    change IsIso (pullback.snd (𝟙 _ ≫ U.ι) (genericPointInclusion X))
    exact isIso_pullback_snd_of_factors _ _
      (IsOpenImmersion.lift U.ι _ (range_genericPointInclusion_subset U)) (by simp)
  exact isTerminalOfIsIsoHom _

/-- **Restriction to `U` after direct image along the generic point, then global sections over
`U`, is global sections over `η`.** -/
def etaleAbelianDirectImageCompRestrictionCompGlobalSectionsIso :
    etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X) ⋙
        (etaleRestriction.{u, u + 1} U.ι ⋙
          Sheaf.Γ (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}) ≅
      Sheaf.Γ (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}
        (isTerminalEtaleMkId (U : Scheme.{u})))) ≪≫
    (Sheaf.ΓNatIsoSheafSections (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminal_smallEtaleBaseChange_smallEtaleCompose_terminal U)).symm

/-- **Stacks 03RK on a nonempty open of a smooth curve.** Let `X` be a smooth curve over an
algebraically closed field, `j : η ⟶ X` the inclusion of its generic point and `U ⊆ X` a nonempty
open. Then `H^p_étale(U, (j_* 𝐆_{m,η})|_U) = 0` for every `p ≥ 1`. -/
theorem subsingleton_sheafH_etaleRestriction_genericPointDirectImage {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (U : X.Opens) [Nonempty U] (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleRestriction.{u, u + 1} U.ι).obj
      ((genericPointDirectImage.{u, u + 1} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)))) p) := by
  let := functionFieldAlgebra k g
  have : ∀ Y : Scheme.{u}, (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    fun Y => Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} Y.smallEtaleTopology
  have : (etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects _
  have h03RJ := isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one k
    (trdeg_functionField_eq_one k g)
  let G := Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)
  let J := etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)
  let R := etaleRestriction.{u, u + 1} U.ι
  let ΓU := Sheaf.Γ (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    (U : Scheme.{u}).smallEtaleTopology _ p]
  have e₁ : ((R ⋙ ΓU).rightDerived p).obj (J.obj G) ≅ (ΓU.rightDerived p).obj (R.obj (J.obj G)) :=
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso R ΓU p).app (J.obj G)
  have e₂ : ((J ⋙ (R ⋙ ΓU)).rightDerived p).obj G ≅ ((R ⋙ ΓU).rightDerived p).obj (J.obj G) :=
    Stacks.RightDerivedComp.objIso J (InjectiveResolution.of G)
      (fun q hq => h03RJ q hq) (R ⋙ ΓU) p
  have e₃ : ((J ⋙ (R ⋙ ΓU)).rightDerived p).obj G ≅
      ((Sheaf.Γ (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
        p).obj G :=
    (ModuleSheafCohomology.rightDerivedIso
      (etaleAbelianDirectImageCompRestrictionCompGlobalSectionsIso U) p).app G
  exact IsZero.of_iso
    ((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
      (Spec X.functionField).smallEtaleTopology _ p).1
      (subsingleton_sheafH_multiplicativeSheaf_spec_functionField k g p hp))
    (e₁.symm ≪≫ e₂.symm ≪≫ e₃)

end Stacks.EtaleCohomology

end

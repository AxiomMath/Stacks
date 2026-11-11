module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.GlobalDetIso
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.PullbackIso

/-!
# The determinant functor commutes with pullback

Let `f : X ⟶ Y` be a morphism of schemes and `K` a perfect object of `D(𝒪_Y)` of Tor amplitude in
`[-1, 0]`. Then `Lf^*K` is a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`
(`AlgebraicGeometry.DeterminantTwoTerm.isPerfectTwoTermAmplitude_derivedPullback`), and for the
determinant functor `AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor` of Stacks 0FJX there
is a canonical identification `f^* det(K) ≅ det(Lf^*K)`: over affine opens `W ⊆ f⁻¹V` it is the
base change `Γ(X, W) ⊗_{Γ(Y, V)} det(M_V) ≅ det(M'_W)` of the determinants of More on Algebra,
Section 0FJI of the complexes `M_V` and `M'_W` representing `K` on `V` and `Lf^*K` on `W`. If `K`
has rank `0`, the canonical global section `δ(K)` pulls back to `δ(Lf^*K)` (Stacks 0FJY).

The identification is the one of
`AlgebraicGeometry.DeterminantTwoTerm.pullbackDetIso`, for the determinant glued from the local
determinants, transported along the isomorphism
`AlgebraicGeometry.DeterminantTwoTerm.detModuleIso` of that determinant with the value of the
determinant functor.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.pullbackDeterminantIso`: `f^* det(K) ≅ det(Lf^*K)`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.pullbackDeterminantIso_hom_pullbackSection`: the
  identification on affine opens is the base change of local determinants.
* `AlgebraicGeometry.DeterminantTwoTerm.pullbackDeterminantIso_hom_determinantSection`: for `K` of
  rank zero, `δ(K)` pulls back to `δ(Lf^*K)`.

## References

* [Stacks Project, Remark 36.39.2 (Tag 0FJY)](https://stacks.math.columbia.edu/tag/0FJY)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite TwoTermDeterminant

namespace AlgebraicGeometry.DeterminantTwoTerm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (K : PerfectTwoTermAmplitude Y)

/-- If `K` has rank zero, so does `Lf^*K`. -/
theorem isRankZeroOn_pullbackObj {K : PerfectTwoTermAmplitude Y} (hK : IsRankZeroOn K) :
    IsRankZeroOn (pullbackObj f K) :=
  (isRankZero_pullbackObj f K (isRankZero_of_isRankZeroOn hK)).isRankZeroOn

/-- **The determinant functor commutes with pullback.** For a morphism of schemes `f : X ⟶ Y` and
a perfect object `K` of `D(𝒪_Y)` of Tor amplitude in `[-1, 0]`, the canonical identification
`f^* det(K) ≅ det(Lf^*K)` of the values of the determinant functor of Stacks 0FJX. -/
@[stacks 0FJY "(b) the canonical identification f^*det(K) → det(Lf^*K), for the determinant
functor of Lemma 0FJX (determinantFunctor)"]
def pullbackDeterminantIso :
    (Scheme.Modules.pullback f).obj ((determinantFunctor Y).obj ⟨K⟩).of.obj ≅
      ((determinantFunctor X).obj ⟨pullbackObj f K⟩).of.obj :=
  (Scheme.Modules.pullback f).mapIso (detModuleIso K).symm ≪≫ pullbackDetIso f K ≪≫
    detModuleIso (pullbackObj f K)

/-- The identification `f^* det(K) ≅ det(Lf^*K)` is the composite of the identification for the
determinant glued from the local determinants with the isomorphisms of `detModuleIso`. -/
theorem pullbackDeterminantIso_hom_app (W : X.Opens)
    (b : ((Scheme.Modules.pullback f).obj ((determinantFunctor Y).obj ⟨K⟩).of.obj).val.obj
      (op W)) :
    (pullbackDeterminantIso f K).hom.val.app (op W) b =
      (detModuleIso (pullbackObj f K)).hom.val.app (op W)
        ((pullbackDetIso f K).hom.val.app (op W)
          (((Scheme.Modules.pullback f).map (detModuleIso K).inv).val.app (op W) b)) :=
  rfl

/-- **The identification `f^* det(K) ≅ det(Lf^*K)` is canonical: on affine opens it is the base
change of local determinants.** For affine opens `V ⊆ Y` and `W ⊆ f⁻¹V`, it sends the pullback of
a section `a` of `det(K)` over `V` to the section of `det(Lf^*K)` over `W` which is the image of
`a ∈ det(M_V)` under the base change `det(M_V) → Γ(X, W) ⊗_{Γ(Y, V)} det(M_V) = det(M'_W)` of the
determinants of More on Algebra, Section 0FJI; the sections over affine opens are read as
determinant modules through `globalDetSectionsEquiv`. -/
@[stacks 0FJY "(b) the identification f^*det(K) → det(Lf^*K) is canonical: over affine opens
W ⊆ f⁻¹V it is the base change of the determinant of More on Algebra 0FJI of the complex
representing K over V"]
theorem pullbackDeterminantIso_hom_pullbackSection (V : Y.affineOpens) (W : X.affineOpens)
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) (a : Γ(((determinantFunctor Y).obj ⟨K⟩).of.obj, V)) :
    (globalDetSectionsEquiv (pullbackObj f K) W).symm
        ((pullbackDeterminantIso f K).hom.val.app (op (W : X.Opens))
          (Scheme.Modules.pullbackSection f _ V W h a)) =
      pullbackDetMap f K V W h ((globalDetSectionsEquiv K V).symm a) := by
  rw [pullbackDeterminantIso_hom_app]
  refine (congrArg (fun z => (globalDetSectionsEquiv (pullbackObj f K) W).symm
    ((detModuleIso (pullbackObj f K)).hom.val.app (op (W : X.Opens))
      ((pullbackDetIso f K).hom.val.app (op (W : X.Opens)) z)))
    (Scheme.Modules.pullbackSection_naturality f (detModuleIso K).inv V W h a)).trans ?_
  exact ((congrArg (globalDetSectionsEquiv (pullbackObj f K) W).symm
      (detModuleIso_hom_app (pullbackObj f K) W _)).trans
      (LinearEquiv.symm_apply_apply _ _)).trans
    ((detSectionsEquiv_pullbackDetIso_hom f K V W h _).trans
      (congrArg (pullbackDetMap f K V W h) (detSectionsEquiv_detModuleIso_inv_app K V a)))

/-- **The canonical global section pulls back to the canonical global section.** If `K` has rank
zero, the identification `f^* det(K) ≅ det(Lf^*K)` carries the pullback of the canonical global
section `δ(K)` of Stacks 0FJX to `δ(Lf^*K)`. -/
@[stacks 0FJY "(c) if K has rank 0, δ(K) pulls back to δ(Lf^*K) via f^*det(K) → det(Lf^*K), for
the determinant functor of Lemma 0FJX and its canonical section (determinantSection)"]
theorem pullbackDeterminantIso_hom_determinantSection {K : PerfectTwoTermAmplitude Y}
    (hK : IsRankZeroOn K) :
    (pullbackDeterminantIso f K).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ ⊤ ⊤ le_top (determinantSection hK)) =
      determinantSection (isRankZeroOn_pullbackObj f hK) := by
  have hK₀ := isRankZero_of_isRankZeroOn hK
  have hd : (detModuleIso K).inv.val.app (op ⊤) (determinantSection hK) = deltaSection K hK₀ := by
    rw [← detModuleIso_hom_deltaSection K hK₀]
    exact congrArg (fun t => t.val.app (op ⊤) (deltaSection K hK₀)) (detModuleIso K).hom_inv_id
  rw [pullbackDeterminantIso_hom_app]
  refine (congrArg (fun z => (detModuleIso (pullbackObj f K)).hom.val.app (op ⊤)
      ((pullbackDetIso f K).hom.val.app (op ⊤) z))
    ((Scheme.Modules.pullbackSection_naturality f (detModuleIso K).inv ⊤ ⊤ le_top
      (determinantSection hK)).trans
      (congrArg (Scheme.Modules.pullbackSection f (detModule K) ⊤ ⊤ le_top) hd))).trans ?_
  rw [pullbackDetIso_hom_deltaSection, detModuleIso_hom_deltaSection]

end AlgebraicGeometry.DeterminantTwoTerm

end

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MainstreamRepresentability

/-!
# Local constancy of finite type along a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`, with `G` fully faithful. Then
restriction of sheaves along `G`, which is an equivalence
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`), preserves and reflects the property of
being a locally constant sheaf of `Λ`-modules of finite type (Tag 093U, in the form
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`).

The typical use is the comparison of the small étale site of Tag 021B cut out of a big étale site
with Mathlib's small étale site, the inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite` being a
fully faithful dense subsite inclusion.

## Main results

* `Stacks.ConstantSheaf.isConstantFGOver_sheafPushforwardContinuous_iff`: the restriction of `F`
  along `G` is constant with finitely generated value over `W` exactly when `F` is over `G(W)`.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff`:
  the restriction of `F` along `G` is locally constant of finite type exactly when `F` is.

## Implementation notes

The pointwise statement is read through the dense subsite `Over.post G`
(`CategoryTheory.Functor.isDenseSubsite_overPost_of_fullyFaithful`): restriction of
`F|_{G(W)}` along it is, by definition, `(F ∘ G)|_W`, and it carries the constant sheaf to the
constant sheaf because sheafification commutes with restriction along a dense subsite
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`). The global
statement is then a statement about the trivializing sieves
`Stacks.ConstantSheaf.trivSieve`: the trivializing sieve of `F ∘ G` at `W` contains the pullback
along `G` of that of `F` at `G(W)`, and every trivializing sieve of `F` contains the image of one
of `F ∘ G` after restriction to the cover of an object by images of `G`.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w r


namespace Stacks.ConstantSheaf

attribute [local instance] ModuleCat.hasLimitsOfSize

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] [G.Full] [G.Faithful] (Λ : Type r) [Ring Λ]

/-- **Pointwise transport of a constant trivialization.** The restriction of `F` along a fully
faithful dense subsite inclusion `G` becomes, over `W`, the constant sheaf on a finitely generated
module exactly when `F` does over `G(W)`. -/
theorem isConstantFGOver_sheafPushforwardContinuous_iff
    (F : Sheaf K (ModuleCat.{max u v w} Λ)) (W : C) :
    IsConstantFGOver J Λ W ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) ↔
      IsConstantFGOver K Λ (G.obj W) F := by
  have := Functor.isDenseSubsite_overPost_of_fullyFaithful J K G W
  let Φ := (Over.post (X := W) G).sheafPushforwardContinuous (ModuleCat.{max u v w} Λ)
    (J.over W) (K.over (G.obj W))
  have hres : Φ.obj ((K.overPullback (ModuleCat.{max u v w} Λ) (G.obj W)).obj F) ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) W).obj
        ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) :=
    Iso.refl _
  have hconst : ∀ E : ModuleCat.{max u v w} Λ,
      Φ.obj ((constantSheaf (K.over (G.obj W)) (ModuleCat.{max u v w} Λ)).obj E) ≅
        (constantSheaf (J.over W) (ModuleCat.{max u v w} Λ)).obj E := fun E ↦
    ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (J.over W) (K.over (G.obj W))
      (Over.post (X := W) G) (ModuleCat.{max u v w} Λ)).app
        ((Functor.const (Over (G.obj W))ᵒᵖ).obj E)).symm
  constructor
  · rintro ⟨E, hE, ⟨δ⟩⟩
    exact ⟨E, hE, ⟨Φ.preimageIso (hconst E ≪≫ δ ≪≫ hres.symm)⟩⟩
  · rintro ⟨E, hE, ⟨ε⟩⟩
    exact ⟨E, hE, ⟨(hconst E).symm ≪≫ Φ.mapIso ε ≪≫ hres⟩⟩

/-- **Local constancy of finite type along a dense subsite** (Tag 093U). For a fully faithful
dense subsite inclusion `G : (C, J) ⥤ (D, K)`, the restriction along `G` of a sheaf `F` of
`Λ`-modules on `D` is locally constant of finite type exactly when `F` is. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff
    (F : Sheaf K (ModuleCat.{max u v w} Λ)) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ
        ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) ↔
      IsFiniteTypeLocallyConstantModuleSheaf K Λ F := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  have := Functor.IsDenseSubsite.isLocallyFull J K G
  simp only [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem]
  constructor
  · intro h T
    refine trivSieve_mem_of_cover (G.is_cover_of_isCoverDense K T) ?_
    rintro Y g ⟨s⟩
    change (trivSieve K Λ F (G.obj s.obj)).pullback s.lift ∈ K Y
    refine K.pullback_stable _ (K.superset_covering ?_
      ((G.functorPushforward_mem_iff J K).2 (h s.obj)))
    rintro Z a ⟨V, v, b, hv, rfl⟩
    exact ((isConstantFGOver_sheafPushforwardContinuous_iff J K G Λ F V).1 hv).restrict b
  · intro h U
    refine J.superset_covering ?_ ((G.functorPushforward_mem_iff J K).1
      (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨_, h (G.obj U)⟩))
    intro V v hv
    exact (isConstantFGOver_sheafPushforwardContinuous_iff J K G Λ F V).2 hv

end Stacks.ConstantSheaf

end

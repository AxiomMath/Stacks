module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartDescentCompat
public import StacksFrontier.AlgebraicGeometry.Descent.ModulePullbackPreimageChart

/-!
# The two comparisons of the inverse image of the descended bundle with the bundle

Let `b : X' ⟶ X`, let `U ⊔ V = ⊤` with `b` invertible over `V`, and let `G` be a module on `X'`
that is free on `b ⁻¹ᵁ U` through `α : 𝒪_{X'}^{⊕I} ⟶ G`. Given a module `N` on `X` whose
restriction to `U` is free and whose restriction to `V` is the restriction of `G` along the
section `AlgebraicGeometry.freeChartBaseSection` of `b`, this file constructs isomorphisms between
the restrictions of the inverse image `b^*N` and of `G` to `b ⁻¹ᵁ U` and to `b ⁻¹ᵁ V`.

## Main definitions

* `AlgebraicGeometry.pullbackSectionRestrictIso`: the inverse image along `b ∣_ V` of the
  restriction of `G` along the section is the restriction of `G` to `b ⁻¹ᵁ V`.
* `AlgebraicGeometry.pullbackFreeChartIso`: the isomorphism between the restriction of `b^*N` and
  the restriction of the free module on `X'`, over the preimage of an open on which `N` is
  trivialised.
* `AlgebraicGeometry.pullbackFreeChartCompIso`: the isomorphism between the restrictions of `b^*N`
  and of `G` over the preimage of an open on which `N` is trivialised.
* `AlgebraicGeometry.pullbackSectionChartIso`: the isomorphism between the restrictions of `b^*N`
  and of `G` over the preimage of `V`.
* `AlgebraicGeometry.preimageChartIso`: the two isomorphisms as one family indexed by `ULift Bool`.

## Main results

* `AlgebraicGeometry.morphismRestrict_comp_freeChartBaseSection`: the restriction of `b` to `V`,
  followed by its section, is the inclusion of the preimage of `V`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {U V : X.Opens}

/-- The restriction of `b` to `V`, followed by the section of `b` over `V`, is the inclusion of
the preimage of `V`. -/
@[simp] theorem morphismRestrict_comp_freeChartBaseSection [IsIso (b ∣_ V)] :
    (b ∣_ V) ≫ freeChartBaseSection b V = (b ⁻¹ᵁ V).ι := by
  rw [freeChartBaseSection, IsIso.hom_inv_id_assoc]

/-- The inverse image along `b ∣_ V` of the restriction of `G` along the section of `b` over `V`
is isomorphic to the restriction of `G` to `b ⁻¹ᵁ V`. -/
def pullbackSectionRestrictIso [IsIso (b ∣_ V)] (G : X'.Modules) :
    (Scheme.Modules.pullback (b ∣_ V)).obj
        (Scheme.Modules.restrict G (freeChartBaseSection b V)) ≅
      Scheme.Modules.restrict G (b ⁻¹ᵁ V).ι :=
  (Scheme.Modules.pullback (b ∣_ V)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (freeChartBaseSection b V)).app G) ≪≫
    pullbackCompIsoOfEq (b ∣_ V) (freeChartBaseSection b V)
      (morphismRestrict_comp_freeChartBaseSection b) G ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ V).ι).app G).symm

variable {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- The isomorphism between the restriction of `b^*N` to `b ⁻¹ᵁ W` and the restriction of the
free module on `X'` to `b ⁻¹ᵁ W`, for an open `W` of `X` on which `N` is trivialised by `τ`. -/
def pullbackFreeChartIso (W : X.Opens) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N) (b ⁻¹ᵁ W).ι ≅
      Scheme.Modules.restrict (_root_.SheafOfModules.free.{u} I) (b ⁻¹ᵁ W).ι :=
  restrictPullbackPreimageIso b W N ≪≫
    (Scheme.Modules.pullback (b ∣_ W)).mapIso τ ≪≫
    Scheme.Modules.pullbackFreeIso (b ∣_ W) I ≪≫
    (Stacks.Modules.restrictFreeIso (b ⁻¹ᵁ W).ι I).symm

/-- The isomorphism between the restrictions of `b^*N` and of `G` to `b ⁻¹ᵁ W`, for an open `W`
of `X` on which `N` is trivialised by `τ` and over whose preimage `α` is invertible:
`AlgebraicGeometry.pullbackFreeChartIso` followed by the restriction of `α`. -/
def pullbackFreeChartCompIso (W : X.Opens) (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W).ι).map α)) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N) (b ⁻¹ᵁ W).ι ≅
      Scheme.Modules.restrict G (b ⁻¹ᵁ W).ι :=
  haveI := hα
  pullbackFreeChartIso b W N τ ≪≫
    asIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W).ι).map α)

/-- The isomorphism between the restrictions of `b^*N` and of `G` to `b ⁻¹ᵁ V`, where `b` is
invertible over `V` and `σ` identifies the restriction of `N` to `V` with the restriction of `G`
along the section of `b`. -/
def pullbackSectionChartIso [IsIso (b ∣_ V)] (N : X.Modules)
    (σ : Scheme.Modules.restrict N V.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V)) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N) (b ⁻¹ᵁ V).ι ≅
      Scheme.Modules.restrict G (b ⁻¹ᵁ V).ι :=
  restrictPullbackPreimageIso b V N ≪≫
    (Scheme.Modules.pullback (b ∣_ V)).mapIso σ ≪≫
    pullbackSectionRestrictIso b G

/-- The isomorphisms between the restrictions of `b^*N` and of `G` to the preimages of the opens
`AlgebraicGeometry.TwoOpensGlue.opn U V i`, as one family indexed by `ULift Bool`:
`AlgebraicGeometry.pullbackFreeChartCompIso` over `U` and
`AlgebraicGeometry.pullbackSectionChartIso` over `V`. -/
def preimageChartIso [IsIso (b ∣_ V)] {N : X.Modules}
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α))
    (κ : ∀ i, Scheme.Modules.restrict N (TwoOpensGlue.opn U V i).ι ≅
      TwoOpensGlue.mdl U V (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
        (Scheme.Modules.restrict G (freeChartBaseSection b V)) i) :
    ∀ i, Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N)
        (b ⁻¹ᵁ TwoOpensGlue.opn U V i).ι ≅
      Scheme.Modules.restrict G (b ⁻¹ᵁ TwoOpensGlue.opn U V i).ι
  | ⟨false⟩ => pullbackFreeChartCompIso b α U N (κ ⟨false⟩) hα
  | ⟨true⟩ => pullbackSectionChartIso (V := V) b N (κ ⟨true⟩)

end AlgebraicGeometry

end

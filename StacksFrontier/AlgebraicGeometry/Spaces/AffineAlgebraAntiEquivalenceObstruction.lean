module

public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# A size obstruction to the affine-algebra anti-equivalence

`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is, for a big fppf site `B` and a base
scheme `S` contained in it, an anti-equivalence between the algebraic spaces affine over `X` and
the quasi-coherent sheaves of commutative `𝒪_X`-algebras, for every algebraic space `X` of the
site at once (Stacks 081V). The two sides are bounded differently. For any `Y` over `X` the
sections of `f_* 𝒪_Y` over an étale chart of `X` are fewer than `B.cutoff`, while
`AlgebraicGeometry.Space.AlgebraSheaf.IsQuasicoherent` imposes no cardinality bound. So a single
quasi-coherent algebra with at least `B.cutoff` sections over an étale chart rules out every such
anti-equivalence.

## Main results

* `AlgebraicGeometry.Space.mk_sections_lt_cutoff`: the regular functions on an open of a scheme
  contained in `B` are fewer than `B.cutoff`.
* `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections`:
  a quasi-coherent `𝒪_X`-algebra with at least `B.cutoff` sections over an étale chart of an
  algebraic space `X` makes `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence B S hS`
  uninhabited.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_free` and
  `AlgebraicGeometry.Space.le_mk_sections_free`: the free module of any rank is quasi-coherent,
  and over an affine chart carrying a nonzero ring of functions its sections number at least
  its rank.
* `AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections`: on an algebraic
  space with an affine chart whose regular functions are not the zero ring there is a
  quasi-coherent module with at least `B.cutoff` sections over that chart.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The regular functions on any open of a scheme contained in a big fppf site are fewer than
the cutoff. -/
theorem mk_sections_lt_cutoff {T : Scheme.{u}} (hT : B.Contains T) (U : T.Opens) :
    #Γ(T, U) < B.cutoff :=
  (Scheme.mk_sections_le_two_pow_size T U).trans_lt (B.cutoff_isStrongPrelimit hT)

/-- A quasi-coherent algebra with at least `B.cutoff` sections over some étale chart rules out
every affine-algebra anti-equivalence. -/
theorem not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections
    {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1)
    (A : QuasicoherentAlgebra B S hS X)
    (hA : B.cutoff ≤ #(A.obj.right.obj.obj (op V))) :
    ¬ Nonempty (AffineAlgebraAntiEquivalence B S hS) := by
  rintro ⟨E⟩
  set Yop : (AffineOver B S hS X)ᵒᵖ := (E.equivalence X).inverse.obj A with hYop
  have i1 : A ≅ (E.pushforward X).obj Yop :=
    ((E.equivalence X).counitIso.app A).symm ≪≫ (E.pushforwardIso X).app Yop
  have i2 : (quasicoherentAlgebraInclusion B S hS X).obj A ≅
      pushforwardAlgebra B S hS Yop.unop.obj :=
    (quasicoherentAlgebraInclusion B S hS X).mapIso i1 ≪≫ E.pushforward_obj X Yop.unop
  let ev : AlgebraSheaf.{u, u} B S hS X.1 X.2 ⥤ CommRingCat.{u} :=
    AlgebraSheaf.forget (B := B) (S := S) (hS := hS) (F := X.1) (hF := X.2) ⋙
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)
  have h : #(A.obj.right.obj.obj (op V)) =
      #((pushforwardAlgebra B S hS Yop.unop.obj).right.obj.obj (op V)) :=
    mk_congr ((forget CommRingCat.{u}).mapIso (ev.mapIso i2)).toEquiv
  exact absurd (h ▸ hA) (not_le.2 (mk_sections_pushforwardAlgebra_lt_cutoff B S hS
    Yop.unop.obj V))

/-! ### The target side is unbounded already at the level of modules -/

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A free module on the small étale site of an algebraic space is quasi-coherent. -/
theorem isQuasicoherentOnSite_free (I : Type u) :
    (SheafOfModules.free
      (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) I).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_free (B := B) (S := S) (hS := hS) (F := F) (hF := hF) I)

/-- Over an affine chart whose regular functions are not the zero ring, the sections of a free
module are at least as many as its rank. -/
theorem le_mk_sections_free (I : Type u) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W)) (h1 : (1 : chartRing B S hS F hF W) ≠ 0) :
    #I ≤ #((SheafOfModules.free
      (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) I).val.obj (op W)) := by
  have hiso : #(I →₀ chartRing B S hS F hF W) =
      #((SheafOfModules.free
        (R :=
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          ) I).val.obj (op W)) :=
    mk_congr ((forget (ModuleCat.{u} (chartRing B S hS F hF W))).mapIso
      (freeSectionsIsoOfIsAffine B S hS F hF I W hW)).toEquiv
  exact hiso ▸ mk_le_of_injective (Finsupp.single_left_injective (α := I) h1)

/-- On an algebraic space with an affine chart carrying a nonzero ring of functions, there is a
quasi-coherent `𝒪_F`-module with at least `B.cutoff` sections over that chart. -/
theorem exists_isQuasicoherentOnSite_cutoff_le_mk_sections (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W)) (h1 : (1 : chartRing B S hS F hF W) ≠ 0) :
    ∃ M : Modules.{u, u} B S hS F hF,
      M.IsQuasicoherentOnSite ∧ B.cutoff ≤ #(M.val.obj (op W)) :=
  ⟨SheafOfModules.free
      (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) B.cutoff.ord.ToType,
    isQuasicoherentOnSite_free B S hS F hF _,
    (mk_ord_toType B.cutoff).symm.le.trans
      (le_mk_sections_free B S hS F hF _ W hW h1)⟩

end AlgebraicGeometry.Space

end

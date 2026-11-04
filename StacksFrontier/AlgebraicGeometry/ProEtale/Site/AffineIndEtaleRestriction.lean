module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting pro-étale sheaves to the affine ind-étale subsite

For an affine scheme `S` in a chosen big pro-étale site, this file supplies the two things
Stacks 098X needs about the inclusion of the affine ind-étale subsite into the small pro-étale
site of `S`, beyond the geometric input:

* the affine ind-étale site is **essentially small** — unconditionally;
* once the inclusion is a dense subsite, restriction along it preserves sheaves and is an
  **equivalence** on sheaves of sets.

The geometric input of Stacks 098X is that the inclusion is cover dense and that the finite
covering families generate exactly the restricted topology. That rests on the existence of
bounded faithfully flat ind-étale w-contractible extensions (Stacks 0984, and so Stacks 0982),
which this library does not have; so it is taken as a hypothesis here and no `stacks` attribute
is attached. Supplying it turns the two results below into Stacks 098X.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.essentiallySmall`: the affine
  ind-étale site is essentially small.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isDenseSubsite_of_restrictedTopology`: if
  the inclusion is cover dense and its topology is the restricted one, it is a dense subsite.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.inclusion_isContinuous_of_restrictedTopology`:
  under the same hypotheses, restriction along the inclusion preserves sheaves.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction_of_isDenseSubsite`:
  for a dense subsite, restriction of sheaves of sets is an equivalence.

## Implementation notes

Essential smallness is proved by exhibiting every object of the site as a model built from a
map `Y ⟶ S` together with proofs: those models are indexed by a type in universe `u`, and
`AlgebraicGeometry.essentiallySmall_schemeSizeBelow` makes the underlying schemes essentially
small, so `CategoryTheory.EssentiallySmall.of_functor` applies. It is what provides the
structured-arrow limits that the dense-subsite comparison theorem of
`Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv` requires, at an arbitrary universe `v`
of sheaf values enlarged to contain the universe of the underlying schemes.

## References

* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 0984](https://stacks.math.columbia.edu/tag/0984)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : B.Scheme)

private theorem essentiallySmall_schemeSizeBelow_max (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) :
    ObjectProperty.EssentiallySmall.{max u v} (schemeSizeBelow κ) := by
  obtain ⟨Q, hQ, hle⟩ :=
    (essentiallySmall_schemeSizeBelow κ hκ).exists_small_le'
  obtain ⟨α, ⟨e⟩⟩ := (hQ : Small.{u} (Subtype Q)).equiv_small
  exact ⟨Q, Small.mk' (e.trans (Equiv.ulift.{v} (α := α)).symm), hle⟩

namespace AffineIndEtaleProetale

private def affineIndEtaleModelData [IsAffine S.obj] (Y : Scheme.{u}) :=
  {f : Y ⟶ S.obj // IsAffine Y ∧ Y.size < B.cutoff ∧ WeaklyEtale f ∧
    ObjectProperty.ind.{u} (fun C : Under Γ(S.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk f.appTop)}

private noncomputable def affineIndEtaleModel [IsAffine S.obj] {Y : Scheme.{u}}
    (d : affineIndEtaleModelData B S Y) :
  AffineIndEtaleProetale B S := by
  let yB : B.Scheme := ⟨Y, d.2.2.1⟩
  let fB : yB ⟶ S := B.inclusion.preimage
    (show B.inclusion.obj yB ⟶ B.inclusion.obj S from d.1)
  have hfB : B.inclusion.map fB = d.1 :=
    B.inclusion.map_preimage (show B.inclusion.obj yB ⟶ B.inclusion.obj S from d.1)
  let W : SmallProetale B S.obj S.property :=
    ⟨Over.mk fB, by
      change WeaklyEtale (B.inclusion.map fB)
      rw [hfB]
      exact d.2.2.2.1⟩
  refine ⟨W, ?_⟩
  constructor
  · exact d.2.1
  · change ObjectProperty.ind.{u}
      (fun C : Under Γ(S.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk (B.inclusion.map fB).appTop)
    rw [hfB]
    exact d.2.2.2.2

private theorem affineIndEtaleFiber_essentiallySmall [IsAffine S.obj] (Y : Scheme.{u}) :
    ObjectProperty.EssentiallySmall.{max u v}
      (fun U : AffineIndEtaleProetale B S ↦
        Nonempty ((toScheme B S).obj U ≅ Y)) := by
  let models : affineIndEtaleModelData B S Y → AffineIndEtaleProetale B S :=
    fun d ↦ affineIndEtaleModel B S d
  let Q : ObjectProperty (AffineIndEtaleProetale B S) := ObjectProperty.ofObj models
  have _ : Small.{max u v} (affineIndEtaleModelData B S Y) := inferInstance
  have hQ : ObjectProperty.Small.{max u v} Q := inferInstance
  apply ObjectProperty.EssentiallySmall.of_le (Q := Q.isoClosure)
  intro U hU
  rcases hU with ⟨e⟩
  let W := U.obj.obj.left
  let f₀ := B.inclusion.map U.obj.obj.hom
  let f : Y ⟶ S.obj := e.inv ≫ f₀
  have hweak : WeaklyEtale f := by
    have _ : WeaklyEtale e.inv := inferInstance
    have _ : WeaklyEtale f₀ := U.obj.property
    exact inferInstance
  have hind : ObjectProperty.ind.{u}
      (fun C : Under Γ(S.obj, ⊤) ↦ C.hom.hom.Etale) (Under.mk f.appTop) := by
    have happ : ∀ {A A' : Scheme.{u}} (g : A ⟶ A') (h : A' ⟶ A), g ≫ h = 𝟙 A →
        h.appTop ≫ g.appTop = 𝟙 _ := fun g h H ↦ by
      rw [← Scheme.Hom.comp_appTop, H, Scheme.Hom.id_appTop]
    have hs := happ _ _ e.hom_inv_id
    have hcomp : f₀.appTop ≫ e.inv.appTop = f.appTop := by
      simp [f]
    have h₀ : ObjectProperty.ind.{u}
        (fun C : Under Γ(S.obj, ⊤) ↦ C.hom.hom.Etale)
        (Under.mk f₀.appTop) := U.property.2
    have h₀' : MorphismProperty.ind.{u} CommRingCat.etale f₀.appTop :=
      (MorphismProperty.ind_iff_ind_underMk f₀.appTop).2 h₀
    have hcomp' : f.appTop ≫ e.hom.appTop = f₀.appTop := by
      rw [← hcomp, Category.assoc, hs]
      exact Category.comp_id _
    have hs' := happ _ _ e.inv_hom_id
    have hind' := indEtale_of_isSplitEpiFactorization f.appTop f₀.appTop e.hom.appTop e.inv.appTop
      hcomp'.symm hs' h₀'
    exact (MorphismProperty.ind_iff_ind_underMk f.appTop).1 hind'
  have hsize : Y.size < B.cutoff := by
    rw [← Scheme.size_congr e]
    exact U.obj.obj.left.property
  have hY : IsAffine Y := (IsAffine.iff_of_isIso e.hom).mp U.property.1
  let d : affineIndEtaleModelData B S Y := ⟨f, hY, hsize, hweak, hind⟩
  let V : AffineIndEtaleProetale B S := affineIndEtaleModel B S d
  let e' : (toScheme B S).obj U ≅
      (toScheme B S).obj V := {
    hom := e.hom
    inv := e.inv
    hom_inv_id := e.hom_inv_id
    inv_hom_id := e.inv_hom_id
  }
  let eB : U.obj.obj.left ≅ V.obj.obj.left := B.inclusion.preimageIso (show
    B.inclusion.obj U.obj.obj.left ≅ B.inclusion.obj V.obj.obj.left from e')
  have hVm : B.inclusion.map V.obj.obj.hom = f := by
    dsimp [V, affineIndEtaleModel]
    exact B.inclusion.map_preimage (show
      B.inclusion.obj V.obj.obj.left ⟶ B.inclusion.obj S from f)
  have htri : eB.hom ≫ V.obj.obj.hom = U.obj.obj.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hVm]
    change B.inclusion.map (B.inclusion.preimage e'.hom) ≫ _ = _
    rw [B.inclusion.map_preimage]
    change e.hom ≫ (e.inv ≫ f₀) = f₀
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  let eOver : U.obj.obj ≅ V.obj.obj := Over.isoMk eB htri
  let eSmall : U.obj ≅ V.obj := ObjectProperty.isoMk _ eOver
  let eApp : U ≅ V := ObjectProperty.isoMk _ eSmall
  refine ⟨V, ?_, ⟨eApp⟩⟩
  have hmodels : ∃ i, models i = V := ⟨d, rfl⟩
  simpa only [Q, ObjectProperty.ofObj_iff] using hmodels

/-- **The affine ind-étale site is essentially small.** For an affine scheme `S` in a chosen big
pro-étale site, the affine ind-étale subsite of its small pro-étale site is equivalent to a
category in the universe of the underlying schemes, enlarged by any universe `v`.

An object of the site is determined by a map `Y ⟶ S` of schemes together with proofs, and the
schemes of size below the cutoff are essentially small by
`AlgebraicGeometry.essentiallySmall_schemeSizeBelow`. -/
theorem essentiallySmall [IsAffine S.obj] :
    EssentiallySmall.{max u v} (AffineIndEtaleProetale B S) := by
  let F := toScheme B S
  have hImage : ObjectProperty.EssentiallySmall.{max u v} F.essImage := by
    have _ : ObjectProperty.EssentiallySmall.{max u v} (schemeSizeBelow B.cutoff) :=
      essentiallySmall_schemeSizeBelow_max B.cutoff (le_of_lt B.aleph0_lt_cutoff)
    apply ObjectProperty.EssentiallySmall.of_le
      (Q := (schemeSizeBelow B.cutoff).isoClosure)
    intro X hX
    obtain ⟨U, ⟨e⟩⟩ := hX
    exact ⟨F.obj U, U.obj.obj.left.property, ⟨e.symm⟩⟩
  exact EssentiallySmall.of_functor F hImage (affineIndEtaleFiber_essentiallySmall B S)

variable {B S}

/-- If the inclusion of the affine ind-étale subsite is cover dense and the topology generated
by its finite covering families is the topology restricted from the small pro-étale site, then
the inclusion is a dense subsite. This is the geometric input of Stacks 098X. -/
theorem isDenseSubsite_of_restrictedTopology [IsAffine S.obj]
    [(inclusion B S).IsCoverDense (SmallProetale.topology B S.obj S.property)]
    (htop : topology B S = (inclusion B S).restrictedTopology
      (SmallProetale.topology B S.obj S.property)) :
    (inclusion B S).IsDenseSubsite (topology B S)
      (SmallProetale.topology B S.obj S.property) := by
  rw [htop]
  infer_instance

/-- Restriction along the inclusion of the affine ind-étale subsite takes pro-étale sheaves to
sheaves, as soon as the inclusion is cover dense and carries the restricted topology. -/
theorem inclusion_isContinuous_of_restrictedTopology [IsAffine S.obj]
    [(inclusion B S).IsCoverDense (SmallProetale.topology B S.obj S.property)]
    (htop : topology B S = (inclusion B S).restrictedTopology
      (SmallProetale.topology B S.obj S.property)) :
    (inclusion B S).IsContinuous (topology B S)
      (SmallProetale.topology B S.obj S.property) := by
  have hcp : CoverPreserving (topology B S)
      (SmallProetale.topology B S.obj S.property) (inclusion B S) := by
    rw [htop]
    exact (inclusion B S).coverPreserving_restrictedTopology
      (SmallProetale.topology B S.obj S.property)
  exact Functor.IsCoverDense.isContinuous (topology B S)
    (SmallProetale.topology B S.obj S.property) (inclusion B S) hcp

/-- **Restriction to a dense affine ind-étale subsite is an equivalence.** For a dense subsite
inclusion, restriction of sheaves of sets along the inclusion of the affine ind-étale subsite is
an equivalence of categories. Together with
`AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isDenseSubsite_of_restrictedTopology` this is
Stacks 098X. -/
theorem isEquivalence_restriction_of_isDenseSubsite [IsAffine S.obj]
    [(inclusion B S).IsContinuous (topology B S)
      (SmallProetale.topology B S.obj S.property)]
    [(inclusion B S).IsDenseSubsite (topology B S)
      (SmallProetale.topology B S.obj S.property)] :
    ((inclusion B S).sheafPushforwardContinuous (Type (max u v))
      (topology B S) (SmallProetale.topology B S.obj S.property)).IsEquivalence := by
  have _ : ∀ X : (SmallProetale B S.obj S.property)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X (inclusion B S).op) (Type (max u v)) := by
    intro X
    have _ : EssentiallySmall.{max u v} (AffineIndEtaleProetale B S) :=
      essentiallySmall.{u, v} B S
    exact CategoryTheory.Limits.HasLimitsOfShape.of_essentiallySmall.{max u v, max u v, u,
      u + 1, max u v, max u v + 1}
      (C := Type (max u v)) (J := StructuredArrow X (inclusion B S).op)
  infer_instance

end AffineIndEtaleProetale

end AlgebraicGeometry.ProEtale

end

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsCofibered
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsRimSchlessinger

/-!
# Continuous representations of a topological group satisfy the Rim–Schlessinger condition

Continuous finite projective representations of a topological group satisfy condition (RS). The
patch is the one for the representations themselves: the full subcategory of continuous objects
is closed under the pullback produced by Stacks 0DVS, because the patched module is a pullback
of the two given modules and the two projections are jointly injective, so an element of `Γ`
acting on the patch by the same automorphism near a given point on both factors acts by that
automorphism on the patch. Joint injectivity comes from a basis of the patched module, whose
coordinates map to the coordinates of the two factors in the fibre product of the coefficient
algebras.

Consequently the deformations of a finite-dimensional continuous representation over the
residue field form a deformation category.

## Main results

* `Deformation.Examples.FiniteProjectiveRepresentation.satisfiesRS_continuousProjection`:
  condition (RS) for the category of continuous finite projective representations.
* `FiniteProjectiveRepresentation.isDeformationCategory_continuousDeformationCategory`, in the
  namespace `Deformation.Examples`: the deformations of a fixed residual continuous
  representation form a deformation category.

## Implementation notes

Continuity of a homomorphism into a discrete group is local constancy, which is the form used
here: the patched representation agrees with a given value on the intersection of the two
neighbourhoods on which the given representations are constant.

Condition (RS) is transported from the ambient category for an arbitrary module universe, so
the statement with a free morphism universe and the one with the module universe independent of
the coefficient-algebra universe both follow; the second is the one the localization at the
special fibre needs.

## References

* [Stacks Project, Tag 0DVV](https://stacks.math.columbia.edu/tag/0DVV)
* [Stacks Project, Tag 0DVS](https://stacks.math.columbia.edu/tag/0DVS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u v w m

/-- A morphism of the representation category exhibits the target module as an extension of
scalars of the source, so two elements of the source with the same image have coordinates with
the same image in the coefficient algebra of the target. -/
private lemma base_repr_eq_of_map_eq {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ} (f : X ⟶ Y)
    {ι : Type*} (b : Module.Basis ι X.base X.carrier) (x y : X.carrier)
    (h : f.map x = f.map y) (i : ι) :
    f.base.hom (b.repr x i) = f.base.hom (b.repr y i) := by
  let : Algebra X.base Y.base := f.base.hom.toAlgebra
  let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
  let : IsScalarTower X.base Y.base Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have he := congrArg (fun value => (f.isBaseChange.basis b).repr value i) h
  change (f.isBaseChange.basis b).repr
    (restrictAddHom f.base.hom.toRingHom f.map f.map_smul x) i =
    (f.isBaseChange.basis b).repr
    (restrictAddHom f.base.hom.toRingHom f.map f.map_smul y) i at he
  rwa [IsBaseChange.basis_repr_comp_apply, IsBaseChange.basis_repr_comp_apply] at he

/-- The two projections of a pullback of Artinian local algebras along a surjection are jointly
injective, since the pullback is the ring of compatible pairs. -/
private lemma eq_of_pullback_proj_eq {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hf₂ : Function.Surjective f₂.hom) {x y : c.pt}
    (h₁ : c.fst.hom x = c.fst.hom y) (h₂ : c.snd.hom x = c.snd.hom y) : x = y := by
  classical
  let h := (ArtinianLocalAlgCat.hasPullback_of_surjective f₁ f₂ (Or.inr hf₂)).1
  let e := (IsPullback.of_isLimit hc).isoIsPullback _ _ h.isPullback
  have he₁ : h.fst.hom (e.hom.hom x) = h.fst.hom (e.hom.hom y) := by
    simpa only [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
      IsPullback.isoIsPullback_hom_fst, e] using h₁
  have he₂ : h.snd.hom (e.hom.hom x) = h.snd.hom (e.hom.hom y) := by
    simpa only [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
      IsPullback.isoIsPullback_hom_snd, e] using h₂
  have he : e.hom.hom x = e.hom.hom y := by
    rw [h.fst_hom] at he₁
    rw [h.snd_hom] at he₂
    exact Subtype.ext (Prod.ext he₁ he₂)
  have hi := congrArg (fun value => e.inv.hom value) he
  change (e.hom ≫ e.inv).hom x = (e.hom ≫ e.inv).hom y at hi
  simpa only [e.hom_inv_id, ArtinianLocalAlgCat.id_hom, AlgHom.id_apply] using hi

/-- The vertex of a pullback cone of representations over a surjection carries a continuous
representation as soon as the two factors do: its module is cut out by the two projections, so
the representation is locally constant where both factors are. -/
private lemma isContinuousRepresentation_pullback {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]
    {X₁ X₂ X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (c : PullbackCone f₁ f₂) (hb : IsLimit (c.map projection))
    (hf₂ : Function.Surjective f₂.base.hom)
    (h₁ : IsContinuousRepresentation X₁.action)
    (h₂ : IsContinuousRepresentation X₂.action) :
    IsContinuousRepresentation c.pt.action := by
  classical
  let : Module.Free c.pt.base c.pt.carrier := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis c.pt.base c.pt.carrier
  have hj {x y : c.pt.carrier} (he₁ : c.fst.map x = c.fst.map y)
      (he₂ : c.snd.map x = c.snd.map y) : x = y :=
    b.repr.injective <| Finsupp.ext fun i => eq_of_pullback_proj_eq (c.map projection) hb hf₂
      (base_repr_eq_of_map_eq c.fst b x y he₁ i) (base_repr_eq_of_map_eq c.snd b x y he₂ i)
  have hl {X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ}
      (h : IsContinuousRepresentation X.action) : IsLocallyConstant X.action.asGroupHom := by
    let : TopologicalSpace (LinearMap.GeneralLinearGroup X.base X.carrier) := ⊥
    have := discreteTopology_bot (LinearMap.GeneralLinearGroup X.base X.carrier)
    exact (IsLocallyConstant.iff_continuous _).2 h
  let : TopologicalSpace (LinearMap.GeneralLinearGroup c.pt.base c.pt.carrier) := ⊥
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro γ
  filter_upwards [(hl h₁).eventually_eq γ, (hl h₂).eventually_eq γ] with δ he₁ he₂
  apply Units.ext
  ext x
  simp only [Representation.asGroupHom_apply]
  apply hj
  · rw [c.fst.equivariant, c.fst.equivariant]
    exact congrArg (fun value => value.val (c.fst.map x)) he₁
  · rw [c.snd.equivariant, c.snd.equivariant]
    exact congrArg (fun value => value.val (c.snd.map x)) he₂

/-- Condition (RS) passes from the category of finite projective representations to its full
subcategory of continuous representations. -/
public theorem satisfiesRS_continuousProjection_of_satisfiesRS {Λ : Type u} {k : Type w}
    {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]
    (hp : SatisfiesRS (projection.{u, v, w, m} (Λ := Λ) (k := k) (Γ := Γ))) :
    SatisfiesRS (continuousProjection.{u, v, w, m} (Λ := Λ) (k := k) (Γ := Γ)) := by
  classical
  refine ⟨continuousProjection_isCofiberedInGroupoids hp.1, fun {X₁ X₂ X} f₁ f₂ hf₂ => ?_⟩
  obtain ⟨c, ⟨hc⟩, ⟨hb⟩⟩ := hp.2 f₁.hom f₂.hom hf₂
  let Y : (continuousObjects.{u, v, w, m} Λ k Γ).FullSubcategory :=
    ⟨c.pt, isContinuousRepresentation_pullback c hb hf₂ X₁.property X₂.property⟩
  let d : PullbackCone f₁ f₂ := PullbackCone.mk
    (ObjectProperty.homMk (X := Y) c.fst)
    (ObjectProperty.homMk (X := Y) c.snd)
    (by apply ObjectProperty.hom_ext; exact c.condition)
  refine ⟨d, ⟨?_⟩, ⟨hb⟩⟩
  exact isLimitOfReflects (continuousObjects.{u, v, w, m} Λ k Γ).ι <|
    (d.isLimitMapConeEquiv (continuousObjects.{u, v, w, m} Λ k Γ).ι).symm
    (IsLimit.ofIsoLimit hc (PullbackCone.ext (Iso.refl _)
      (by change c.fst = 𝟙 _ ≫ c.fst; simp)
      (by change c.snd = 𝟙 _ ≫ c.snd; simp)))

/-- Continuous finite projective representations of a topological group satisfy the
Rim–Schlessinger condition. -/
@[stacks 0DVV "Rim-Schlessinger condition"]
public theorem satisfiesRS_continuousProjection {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ] :
    SatisfiesRS
      (continuousProjection.{u, v, w, max v m} (Λ := Λ) (k := k) (Γ := Γ)) :=
  satisfiesRS_continuousProjection_of_satisfiesRS satisfiesRS_projection

/-- Condition (RS) for continuous finite projective representations, with the module universe
independent of the universe of the coefficient algebras.

This is the form `satisfiesRS_continuousProjection` takes when the morphism universe of `𝒞_Λ`
is the residue-field universe `w`; it is the shape the localization at the special fibre
needs. -/
public theorem satisfiesRS_continuousProjection_carrierUniverse {Λ : Type u} {k : Type w}
    {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ] :
    SatisfiesRS (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ)) :=
  satisfiesRS_continuousProjection_of_satisfiesRS satisfiesRS_projection_carrierUniverse

/-- The deformations of a finite-dimensional continuous representation of a topological group
form a deformation category. -/
@[stacks 0DVV "deformation category"]
public theorem isDeformationCategory_continuousDeformationCategory {Λ : Type u} {k : Type w}
    {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    IsDeformationCategory
      (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)) :=
  isDeformationCategory_objectsOverFunctor_of_baseIso _
    satisfiesRS_continuousProjection_carrierUniverse
    (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀) residueFieldBaseIso

end Deformation.Examples.FiniteProjectiveRepresentation

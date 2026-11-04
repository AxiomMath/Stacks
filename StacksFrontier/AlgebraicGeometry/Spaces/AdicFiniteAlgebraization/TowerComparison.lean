module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport

/-!
# Grothendieck existence on a tower of thickenings, from the completion functor

Let `X` be an algebraic space with a tower of closed subspaces `ι n : Z n ⟶ X` whose ideals act on
every `𝒪_X`-module as the powers `𝓘 ^ (n + 1)` of a quasi-coherent sheaf of ideals. The functor
`Φ : F ↦ (ι n ^* F)_n` from coherent `𝒪_X`-modules to coherent systems on the tower is, after the
fully faithful direct image `Ψ` to `Coh(X, 𝓘)`, the completion functor
(`AlgebraicGeometry.Space.thickeningRestrictionCompPushforwardIso`). This file reads the two
halves of Grothendieck's existence theorem — full faithfulness on a pair of modules, and
essential surjectivity onto the systems with proper support — from the completion functor
over to `Φ`, one pair and one object at a time. This is the passage from Stacks 08BE to its
reformulation Stacks 08BF.

## Main results

* `AlgebraicGeometry.Space.bijective_thickeningRestriction_map_of_bijective`: `Φ` is bijective
  on `Hom(M, N)` whenever the completion functor is.
* `AlgebraicGeometry.Space.exists_iso_thickeningRestriction_of_mem_essImage`: a system whose
  direct image is a completion is a restriction.
* `AlgebraicGeometry.Space.exists_hasProperSupport_iso_thickeningRestriction`: a system whose
  direct image has proper support is the restriction of a coherent module with proper support,
  as soon as the completion functor is essentially surjective onto the systems with proper
  support.

## References

* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {Z : ℕ → AlgebraicSpaces B S hS} (ι : ∀ n, Z n ⟶ X)
  (t : ∀ n, Z n ⟶ Z (n + 1)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
  (hi : ∀ n, IsClosedImmersion B S hS (ι n).hom)
  {𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule}
  [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
  (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
    kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
  (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

include hi hker in
/-- **Full faithfulness on one pair, from the completion functor to the tower.** If the
completion functor is bijective on `Hom(M, N)`, so is the restriction `Φ` to the thickenings. -/
theorem bijective_thickeningRestriction_map_of_bijective
    {M N : CoherentModules.{u, u} B S hS X.1 X.2}
    (h : Function.Bijective
      (fun a : M ⟶ N => (completionFunctor B S hS X.1 X.2 𝓘 hI).map a)) :
    Function.Bijective
      (fun a : M ⟶ N => (thickeningRestriction B S hS ι t hι hZ).map a) := by
  let Φ := thickeningRestriction B S hS ι t hι hZ
  let Ψ := thickeningPushforward B S hS ι t hι hi hX.out hker
  let e := thickeningRestrictionCompPushforwardIso B S hS ι t hι hi hZ hker hI
  have hΨ := thickeningPushforwardFullyFaithful B S hS ι t hι hi hX.out hker
  have hcomp : Function.Bijective (fun a : M ⟶ N => Ψ.map (Φ.map a)) := by
    have hconj : (fun a : M ⟶ N => Ψ.map (Φ.map a)) =
        (Iso.homCongr (e.app M).symm (e.app N).symm) ∘
          (fun a : M ⟶ N => (completionFunctor B S hS X.1 X.2 𝓘 hI).map a) := by
      funext a
      simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv]
      rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
      rfl
    rw [hconj]
    exact (Iso.homCongr (e.app M).symm (e.app N).symm).bijective.comp h
  exact (Function.Bijective.of_comp_iff' (hΨ.map_bijective _ _) _).mp hcomp

include hi hker in
/-- **A system whose direct image to `Coh(X, 𝓘)` is a completion is a restriction.** -/
theorem exists_iso_thickeningRestriction_of_mem_essImage
    (A : ThickeningCoherentSystem B S hS Z t) (M : CoherentModules.{u, u} B S hS X.1 X.2)
    (e : (completionFunctor B S hS X.1 X.2 𝓘 hI).obj M ≅
      (thickeningPushforward B S hS ι t hι hi hX.out hker).obj A) :
    Nonempty ((thickeningRestriction B S hS ι t hι hZ).obj M ≅ A) :=
  ⟨(thickeningPushforwardFullyFaithful B S hS ι t hι hi hX.out hker).preimageIso
    ((thickeningRestrictionCompPushforwardIso B S hS ι t hι hi hZ hker hI).app _ ≪≫ e)⟩

/-- The lowest term of the direct image of a system on the tower is the direct image of the
lowest term of the system. -/
theorem thickeningPushforward_obj_obj_obj_zero (A : ThickeningCoherentSystem B S hS Z t) :
    ((thickeningPushforward B S hS ι t hι hi hX.out hker).obj A).obj.obj (op 0) =
      (modulePushforward B S hS (ι 0)).obj (A.term 0).obj :=
  rfl

attribute [local instance] pointTopology in
include hi hker in
/-- **Essential surjectivity onto the systems with proper support, from the completion functor to
the tower.** Let `g : X ⟶ Y` be locally of finite type and suppose the completion functor is
essentially surjective from the coherent `𝒪_X`-modules with support proper over `Y` onto the
coherent adic systems whose lowest term has support proper over `Y`. Then a system `(F_n)` on the
tower such that `(ι 0)_* F_0` has support proper over `Y` is the restriction of a coherent
`𝒪_X`-module with support proper over `Y`. -/
theorem exists_hasProperSupport_iso_thickeningRestriction {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (g : X.1 ⟶ Y) (hg : IsLocallyOfFiniteType B S hS g)
    [(completionFunctorProperOver B S hS X.1 Y X.2 hY g hg 𝓘 hI).EssSurj]
    (A : ThickeningCoherentSystem B S hS Z t)
    (hA : HasProperSupport B S hS X.2 hY g hg
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS (ι 0)).obj (A.term 0).obj))) :
    ∃ M : CoherentModules.{u, u} B S hS X.1 X.2,
      HasProperSupport B S hS X.2 hY g hg ((SheafOfModules.toSheaf _).obj M.obj) ∧
        Nonempty ((thickeningRestriction B S hS ι t hι hZ).obj M ≅ A) := by
  let E : CoherentAdicSystemsProperOver B S hS X.2 hY g hg 𝓘 :=
    ⟨(thickeningPushforward B S hS ι t hι hi hX.out hker).obj A, hA⟩
  let G := (completionFunctorProperOver B S hS X.1 Y X.2 hY g hg 𝓘 hI).objPreimage E
  let eG := (completionFunctorProperOver B S hS X.1 Y X.2 hY g hg 𝓘 hI).objObjPreimageIso E
  exact ⟨G.obj, G.property, exists_iso_thickeningRestriction_of_mem_essImage B S hS ι t hι hi hZ
    hker hI A G.obj ((ObjectProperty.ι _).mapIso eG)⟩

end AlgebraicGeometry.Space

end

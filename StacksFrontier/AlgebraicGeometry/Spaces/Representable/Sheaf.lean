module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Representable transformations preserve the sheaf property

A representable transformation of set-valued presheaves on the big fppf site over a scheme
has a sheaf as its source whenever its target is a sheaf.

## Main results

* `AlgebraicGeometry.Space.isSheaf_of_relativelyRepresentable`: the source of a
  representable transformation into a sheaf on the big fppf site over `S` is a sheaf.

## References

* [Stacks Project, Tag 02WD](https://stacks.math.columbia.edu/tag/02WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ v₁

namespace AlgebraicGeometry.Space

/-- A representable transformation into a sheaf on the big fppf site over `S` has a sheaf as its
source. -/
@[stacks 02WD]
public theorem isSheaf_of_relativelyRepresentable
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a)
    (hG : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) G) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) F := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := by
    show (B.topology.over (B.obj hS)).Subcanonical
    infer_instance
  have hG' : Presieve.IsSheaf J G :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type J G).1 hG
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro X R hR s hs
  let fNat : R.functor ⟶ F := AlgebraicGeometry.compatibleFamilyToNatTrans R s hs
  obtain ⟨gG, hgG, hgGuniq⟩ :=
    Presieve.isSheafFor_iff_yonedaSheafCondition.1 (hG' R hR) (fNat ≫ a)
  let ξ : G.obj (Opposite.op X) := yonedaEquiv gG
  let v : yoneda.obj X ⟶ G := yonedaEquiv.symm ξ
  have hv : v = gG := by simp [v, ξ]
  let H := pullback v a
  let _ : H.IsRepresentable :=
    (CategoryTheory.yoneda_relativelyRepresentable_iff_pullback_representable a).1 ha X ξ
  let k : R.functor ⟶ H := pullback.lift R.functorInclusion fNat (by simpa [hv] using hgG)
  obtain ⟨gH, hgH, hgHuniq⟩ := Presieve.isSheafFor_iff_yonedaSheafCondition.1
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) H R hR) k
  let t₀ := yonedaEquiv (gH ≫ pullback.snd v a)
  refine ⟨t₀, ?_, ?_⟩
  · intro Y f hf
    have hres : R.functorInclusion ≫ (gH ≫ pullback.snd v a) = fNat := by
      rw [← Category.assoc, hgH, pullback.lift_snd]
    have heq := congrArg (fun q : R.functor ⟶ F => q.app (Opposite.op Y) ⟨f, hf⟩) hres
    change (pullback.snd v a).app (Opposite.op Y) (gH.app (Opposite.op Y) f) =
      (fNat.app (Opposite.op Y)) ⟨f, hf⟩ at heq
    simpa [t₀, fNat, AlgebraicGeometry.compatibleFamilyToNatTrans,
      CategoryTheory.map_yonedaEquiv] using heq
  · intro t ht
    let tYon : yoneda.obj X ⟶ F := yonedaEquiv.symm t
    have htrestrict : R.functorInclusion ≫ tYon = fNat := by
      ext Y z
      rcases z with ⟨f, hf⟩
      show F.map f.op t = fNat.app Y ⟨f, hf⟩
      simpa [fNat, AlgebraicGeometry.compatibleFamilyToNatTrans] using ht f hf
    have hta : tYon ≫ a = gG := hgGuniq (tYon ≫ a) <| by
      simpa [Category.assoc] using congrArg (fun q : R.functor ⟶ F => q ≫ a) htrestrict
    let k' : yoneda.obj X ⟶ H := pullback.lift (𝟙 (yoneda.obj X)) tYon (by
      rw [Category.id_comp, hv, hta])
    have hk' : R.functorInclusion ≫ k' = k := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, k', k, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, htrestrict]
    have hmap : tYon = gH ≫ pullback.snd v a := by
      have hh := congrArg (fun q => q ≫ pullback.snd v a) (hgHuniq k' hk')
      dsimp only [k'] at hh
      simpa only [pullback.lift_snd] using hh
    simpa [tYon, t₀] using congrArg yonedaEquiv hmap

end AlgebraicGeometry.Space

end

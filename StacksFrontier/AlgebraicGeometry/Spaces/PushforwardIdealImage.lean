module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitTensorMultiplication

/-!
# The image of the direct image of an ideal under a locally surjective ring map

Let `f : Y ⟶ X` and `g : Z ⟶ X` be morphisms of algebraic spaces, `f` affine, and let
`t : g_*𝒪_Z ⟶ f_*𝒪_Y` be a map of `𝒪_X`-modules which is multiplicative on sections and
locally surjective — for instance the map induced by a closed immersion `Y ⟶ Z` over `X`.  For a
sheaf of ideals `𝒥 ⊆ 𝒪_Z`, the image of `g_*𝒥` under `t` is closed under multiplication by the
sections of `f_*𝒪_Y`: locally a section of `f_*𝒪_Y` is `t(a)` and a section of the image is
`t(n)` with `n ∈ g_*𝒥`, and `t(a) t(n) = t(a n)` with `a n ∈ g_*𝒥`.  So, when that image is
quasi-coherent, it is the direct image `f_*ℐ` of a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`, of
finite type when the image is (`AlgebraicGeometry.Space.exists_ideal_pushforwardSubmodule_eq`).

## Main results

* `Space.mul_mem_imageSubmodule_of_isLocallySurjective`: the image is closed under
  multiplication by sections of `f_*𝒪_Y`.
* `Space.exists_ideal_pushforwardSubmodule_eq_imageSubmodule_of_isLocallySurjective`: the image
  is the direct image of a quasi-coherent sheaf of ideals.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} {f : Y ⟶ X} {hf : yoneda.relativelyRepresentable f.hom}
  {g : Z ⟶ X} {hg : yoneda.relativelyRepresentable g.hom}
  (t : chartBaseChangeStructureModule B S hS g hg ⟶ chartBaseChangeStructureModule B S hS f hf)
  (J : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z.1 Z.2)).Submodule)

/-- **The image of the direct image of an ideal under a multiplicative, locally surjective map is
closed under multiplication.**  If `t : g_*𝒪_Z ⟶ f_*𝒪_Y` is multiplicative on sections and
locally surjective, `b` is a section of `f_*𝒪_Y` and `m` a section of the image of `g_*𝒥` under
`t`, then `b * m` is a section of that image. -/
theorem mul_mem_imageSubmodule_of_isLocallySurjective
    (hmul : ∀ (Q : SmallEtale B S hS X.1)
      (a b : chartSectionsRing B S hS Z ((smallBaseChange B S hS g hg).obj Q)),
        t.val.app (op Q) (a * b) =
          @HMul.hMul (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
            (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
            (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)) instHMul
            (t.val.app (op Q) a) (t.val.app (op Q) b))
    (hsurj : ∀ (Q : SmallEtale B S hS X.1)
      (b : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)),
        ∃ R : Sieve Q, R ∈ SmallEtale.topology B S hS X.1 Q ∧ ∀ ⦃W : SmallEtale B S hS X.1⦄
          (h : W ⟶ Q), R h → ∃ a, t.val.app (op W) a =
            (chartBaseChangeStructureModule B S hS f hf).val.map h.op b)
    (Q : SmallEtale B S hS X.1)
    (b m : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
    (hm : m ∈ (imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t)).obj (op Q)) :
    b * m ∈ (imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t)).obj (op Q) := by
  set ψ := (pushforwardSubmodule B S hS g hg _ J).ι ≫ t with hψ
  obtain ⟨R, hR, hRb⟩ := hsurj Q b
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((SmallEtale.topology B S hS X.1).intersection_covering hm hR)
  rintro W h ⟨hhm, hhb⟩
  refine (sieveOfSection_rangeSubmodule_apply ψ (b * m) h).2 ?_
  obtain ⟨⟨x, hx⟩, hxm⟩ := (sieveOfSection_rangeSubmodule_apply ψ m h).1 hhm
  obtain ⟨a, ha⟩ := hRb h hhb
  have hres : (chartBaseChangeStructureModule B S hS f hf).val.map h.op (b * m) =
      @HMul.hMul (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj W))
        (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj W))
        (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj W)) instHMul
        ((chartBaseChangeStructureModule B S hS f hf).val.map h.op b)
        ((chartBaseChangeStructureModule B S hS f hf).val.map h.op m) :=
    map_mul ((smallEtaleRingSheaf B S hS Y.1 Y.2).obj.map
      ((smallBaseChange B S hS f hf).map h).op).hom _ _
  have hax : @HMul.hMul (chartSectionsRing B S hS Z ((smallBaseChange B S hS g hg).obj W))
      (chartSectionsRing B S hS Z ((smallBaseChange B S hS g hg).obj W))
      (chartSectionsRing B S hS Z ((smallBaseChange B S hS g hg).obj W)) instHMul a x ∈
      J.obj (op ((smallBaseChange B S hS g hg).obj W)) :=
    (J.obj (op ((smallBaseChange B S hS g hg).obj W))).smul_mem a hx
  refine ⟨⟨_, hax⟩, ?_⟩
  have hxm' : t.val.app (op W) x =
      (chartBaseChangeStructureModule B S hS f hf).val.map h.op m := hxm
  exact (hmul W a x).trans ((congrArg₂ _ ha hxm').trans hres.symm)

/-- **The image of the direct image of an ideal under a multiplicative, locally surjective map is
the direct image of an ideal.**  Let `f : Y ⟶ X` be affine, `t : g_*𝒪_Z ⟶ f_*𝒪_Y` multiplicative
on sections and locally surjective, and `𝒥 ⊆ 𝒪_Z` a sheaf of ideals.  If the image of `g_*𝒥`
under `t` is quasi-coherent, it is `f_*ℐ` for a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`, of
finite type when the image is. -/
theorem exists_ideal_pushforwardSubmodule_eq_imageSubmodule_of_isLocallySurjective
    (haff : IsAffineHom B S hS f.hom)
    (hmul : ∀ (Q : SmallEtale B S hS X.1)
      (a b : chartSectionsRing B S hS Z ((smallBaseChange B S hS g hg).obj Q)),
        t.val.app (op Q) (a * b) =
          @HMul.hMul (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
            (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
            (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)) instHMul
            (t.val.app (op Q) a) (t.val.app (op Q) b))
    (hsurj : ∀ (Q : SmallEtale B S hS X.1)
      (b : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)),
        ∃ R : Sieve Q, R ∈ SmallEtale.topology B S hS X.1 Q ∧ ∀ ⦃W : SmallEtale B S hS X.1⦄
          (h : W ⟶ Q), R h → ∃ a, t.val.app (op W) a =
            (chartBaseChangeStructureModule B S hS f hf).val.map h.op b)
    (hM : (imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t)).toSheafOfModules
      |>.IsQuasicoherentOnSite) :
    ∃ I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite ∧
      (SheafOfModules.IsFiniteTypeOnSite
          ((imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t)).toSheafOfModules :
            Modules.{u, u} B S hS X.1 X.2) →
        SheafOfModules.IsFiniteTypeOnSite
          (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ∧
      pushforwardSubmodule B S hS f hf _ I =
        imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t) :=
  exists_ideal_pushforwardSubmodule_eq B S hS f hf
    (imageSubmodule ((pushforwardSubmodule B S hS g hg _ J).ι ≫ t)) haff
    (mul_mem_imageSubmodule_of_isLocallySurjective t J hmul hsurj) hM

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorPullback

/-!
# The restriction map of the functor of sections is the canonical reduction

Condition (iii) of [Stacks, Tag 07YG] for the example of [Stacks, Tag 07YH] is proved in two
halves which do not meet. The categorical half,
`Deformation.Artin.SectionsSheaf.hasLift_iff_exists_section`, says that an object of `𝒳` over
`Spec A` lifts across a deformation situation exactly when the section of `𝓕_A` it names is in
the image of the restriction map

```
F(A') = H⁰(W_{A'}, 𝓕_{A'}) ⟶ H⁰(W_A, 𝓕_A) = F(A)
```

of the functor `F` of the source. The sheaf-level half,
`Deformation.Artin.SectionsSheaf.exists_section_iff_obstructionClass_eq_zero`, says that a
section of `𝓕_{A'} ⊗_{A'} A` is in the image of the map induced by `A' → A` exactly when its
obstruction class vanishes. The two are about different maps of different modules, and what
stands between them is an identification of the two — the one the docstring of
`hasLift_iff_exists_section` records as missing.

This file settles its first half: **the restriction map of `F` along the base-change immersion
`i : W_A → W_{A'}` is the global-sections component of the canonical reduction
`𝓕_{A'} ⟶ i_* 𝓕_A`**, on the nose. What remains of the identification is therefore a statement
with no sections and no cohomology in it — an equality of two morphisms `𝓕_{A'} ⟶ i_* 𝓕_A` —
and `reductionMapGen_eq_iff` turns that into an equality of two morphisms
`i^* 𝓕_{A'} ⟶ 𝓕_A`, one of which is `Deformation.Artin.SectionsSheaf.baseChangeSheafIso`.

## Main definitions

* `Deformation.Artin.SectionsSheaf.reductionMapGen` — **the canonical reduction
  `𝓕_{A'} ⟶ g_* 𝓕_{A₁}`** with the base-change morphism of schemes `g` as a parameter: the unit
  of the pullback--pushforward adjunction at `g`, followed by the direct image of
  `g^* 𝓕_{A'} ≅ 𝓕_{A₁}`, which is `Deformation.Artin.SectionsSheaf.baseChangeSheafIsoGen`.
* `Deformation.Artin.SectionsSheaf.reductionMap` — its instantiation at the base-change
  immersion of a deformation situation.

## Main results

* `Deformation.Artin.SectionsSheaf.sectionsPresheafOver_map_eq_reductionMapGen` — **the
  restriction map of `F` along any morphism `T' ⟶ T` of schemes over `S` is the reduction map
  on global sections**, and `..sectionsPresheafOver_map_quotHom` is that at `Spec A → Spec A'`.
  It holds by `rfl`: the restriction maps of [Stacks, Tag 03DS] are built from the same unit,
  and the comparison of iterated pullbacks they carry is `baseChangeSheafIsoGen` on the nose.
* `Deformation.Artin.SectionsSheaf.reductionMapGen_eq_iff` — a morphism `𝓕_{A'} ⟶ g_* 𝓕_{A₁}`
  is the reduction map exactly when its adjoint transpose is `baseChangeSheafIsoGen`.

## Implementation notes

The statements are made at a **variable** morphism of schemes over `S` and instantiated
afterwards, and the two concrete instantiations name the comparison through the constants
`baseChangeSheafIso` and `reductionMap` rather than spelling it out. Both are forced, and for the
second the reason is this: a statement that writes `baseChangeSheafIsoGen … (baseChangeMap q (quotHom
φ t)) (baseChangeMap_comp_snd q (quotHom φ t))` out in full is the instantiation of the general
one on the nose, elaborates, and then **fails in the kernel with a deterministic timeout** —
the proof term `baseChangeMap_comp_snd q (quotHom φ t)` appearing in the statement has to be
typechecked afresh there, at a concrete fibre product, which asks for `Limits.getLimitCone`;
behind the constant it is a compiled body the kernel does not revisit. The same statement
written with `baseChangeSheafIso` checks in seconds.

## What is not done

The identification of the reduction map with the third map of the sheaf-level sequence of
clause (2) — that is, of `reductionMap` with

```
𝓕_{A'} ≅ 𝓕_{A'} ⊗_{A'} A' ⟶ 𝓕_{A'} ⊗_{A'} A ≅ i_*(𝓕_A ⊗_A A) ≅ i_* 𝓕_A,
```

the unitor `tensorSheafFunctorObjSelf`, the map induced by `A' → A`, and
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` at `M = A` — is **not** proved
here, and it is what condition (iii) for the source's `𝒳` still waits on. Through
`reductionMapGen_eq_iff` and `Stacks.AffineProjectionFormula.projectionFormulaMap_eq_unit_comp` it
is equivalent to an equality of morphisms `i^* 𝓕_{A'} ⟶ 𝓕_A` whose right-hand side is built from
the comparison of [Stacks, Tag 01CD], the counit of the immersion, [Stacks, Tag 01I9] and the
affine base-change isomorphism of [Stacks, Tag 02KG]; of those four only the first has a
degeneration formula in the library (`Stacks.RingedSpace.unit_comp_comparisonIso_id`).

Nor is the site-level form stated: `Deformation.Artin.SectionsSheaf.sectionsPresheaf` is
`sectionsPresheafOver` precomposed with the site's inclusion, so a statement about its
restriction map along `t.hom.specMap` needs in addition the identification of
`(siteToOver B hS).map t.hom.specMap` with `quotHom`, which is the bookkeeping that
`Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme` governs.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### The canonical reduction, with the base-change morphism as a parameter -/

section ReductionGen

variable {W X X₁ : Scheme.{u}} (s : X ⟶ W) (s₁ : X₁ ⟶ W) (𝓕 : W.Modules) (g : X₁ ⟶ X)

/-- **The canonical reduction `𝓕_{A'} ⟶ g_* 𝓕_{A₁}`** for a morphism `g : W_{A₁} → W_{A'}` over
`W`: the unit of the pullback--pushforward adjunction at `g`, followed by the direct image of
the comparison `g^* 𝓕_{A'} ≅ 𝓕_{A₁}` of
`Deformation.Artin.SectionsSheaf.baseChangeSheafIsoGen`.

At the base-change immersion of a deformation situation this is the map the source means when
it writes the last term of the sequence of clause (2) as `𝓕_A`; its global-sections component
is the restriction map of the functor `F`, which is
`sectionsPresheafOver_map_eq_reductionMapGen`. -/
@[sga "3 VIB 11.6"]
def reductionMapGen (hsnd : g ≫ s = s₁) :
    (Scheme.Modules.pullback s).obj 𝓕 ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback s₁).obj 𝓕) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback s).obj 𝓕) ≫
    (Scheme.Modules.pushforward g).map (baseChangeSheafIsoGen s s₁ 𝓕 g hsnd).hom

/-- **A morphism `𝓕_{A'} ⟶ g_* 𝓕_{A₁}` is the canonical reduction exactly when its adjoint
transpose is `baseChangeSheafIsoGen`.** The reduction map is the image of that comparison under
the adjunction bijection `Hom(g^* 𝓕_{A'}, 𝓕_{A₁}) ≃ Hom(𝓕_{A'}, g_* 𝓕_{A₁})`, so testing a
morphism against it is testing its transpose against a comparison of two pullbacks.

This is the form in which the remaining obligation of condition (iii) is to be discharged: the
candidate is the third map of the sheaf-level sequence of clause (2), and the equality to be
proved is then one of morphisms `g^* 𝓕_{A'} ⟶ 𝓕_{A₁}`. -/
theorem reductionMapGen_eq_iff (hsnd : g ≫ s = s₁)
    (k : (Scheme.Modules.pullback s).obj 𝓕 ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback s₁).obj 𝓕)) :
    reductionMapGen s s₁ 𝓕 g hsnd = k ↔
      (baseChangeSheafIsoGen s s₁ 𝓕 g hsnd).hom =
        (Scheme.Modules.pullback g).map k ≫
          (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
            ((Scheme.Modules.pullback s₁).obj 𝓕) :=
  Adjunction.unit_comp_map_eq_iff (Scheme.Modules.pullbackPushforwardAdjunction g)
    (baseChangeSheafIsoGen s s₁ 𝓕 g hsnd).hom k

end ReductionGen

/-! ### The restriction map of the functor of sections -/

section Sections

variable {S : Scheme.{u}} {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules) [𝓕.IsQuasicoherent]

/-- **The restriction map of the functor `F` of Stacks 07YH is the canonical reduction on
global sections.** The restriction maps of the presheaf of sections of [Stacks, Tag 03DS] are
the unit of the pullback--pushforward adjunction followed by the comparison of the iterated
pullback with the pullback along the composite, read at `⊤`; along the base change of a
morphism `T' ⟶ T` of schemes over `S` that composite is `reductionMapGen`.

So the image of the restriction map — the sections of `𝓕_T` that lift to `W_{T'}`, which is
what `hasLift_iff_exists_section` characterizes a lift by — is the image of the reduction map
on global sections. -/
theorem sectionsPresheafOver_map_eq_reductionMapGen {T T' : Over S} (α : T' ⟶ T) :
    (sectionsPresheafOver q 𝓕).map α.op =
      Scheme.Modules.Hom.app
        (reductionMapGen (pullback.snd T.hom q) (pullback.snd T'.hom q) 𝓕
          (baseChangeMap q α) (baseChangeMap_comp_snd q α)) ⊤ ≫
        (Scheme.Modules.presheaf
            ((Scheme.Modules.pullback (pullback.snd T'.hom q)).obj 𝓕)).map
          (eqToHom (show (⊤ : (pullback T'.hom q).Opens) =
            (baseChangeMap q α) ⁻¹ᵁ ⊤ by simp)).op :=
  rfl

end Sections

/-! ### The reduction at the base-change immersion of a deformation situation -/

section Reduction

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **The canonical reduction `𝓕_{A'} ⟶ i_* 𝓕_A`** along the base-change immersion
`i : W_A → W_{A'}` of a deformation situation: `reductionMapGen` at that immersion. -/
def reductionMap :
    (Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕 ⟶
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕) :=
  reductionMapGen (pullback.snd (Over.mk t).hom q) (pullback.snd (quotOver φ t).hom q) 𝓕
    (baseChangeMap q (quotHom φ t)) (baseChangeMap_comp_snd q (quotHom φ t))

/-- **The restriction map `F(A') ⟶ F(A)` of the functor of sections of Stacks 07YH is the
canonical reduction `𝓕_{A'} ⟶ i_* 𝓕_A` on global sections.** This is
`sectionsPresheafOver_map_eq_reductionMapGen` at the morphism `Spec A → Spec A'` of a
deformation situation. -/
theorem sectionsPresheafOver_map_quotHom [𝓕.IsQuasicoherent] :
    (sectionsPresheafOver q 𝓕).map (quotHom φ t).op =
      Scheme.Modules.Hom.app (reductionMap φ t q 𝓕) ⊤ ≫
        (Scheme.Modules.presheaf ((Scheme.Modules.pullback
            (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).map
          (eqToHom (show (⊤ : (pullback (quotOver φ t).hom q).Opens) =
            (baseChangeMap q (quotHom φ t)) ⁻¹ᵁ ⊤ by simp)).op :=
  sectionsPresheafOver_map_eq_reductionMapGen q 𝓕 (quotHom φ t)

/-- The reduction map at the base-change immersion is the one whose adjoint transpose is
`Deformation.Artin.SectionsSheaf.baseChangeSheafIso`; this is `reductionMapGen_eq_iff` there. -/
theorem reductionMap_eq_iff
    (k : (Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕 ⟶
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)) :
    reductionMap φ t q 𝓕 = k ↔
      (baseChangeSheafIso φ t q 𝓕).hom =
        (Scheme.Modules.pullback (baseChangeMap q (quotHom φ t))).map k ≫
          (Scheme.Modules.pullbackPushforwardAdjunction
              (baseChangeMap q (quotHom φ t))).counit.app
            ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕) :=
  reductionMapGen_eq_iff (pullback.snd (Over.mk t).hom q)
    (pullback.snd (quotOver φ t).hom q) 𝓕 (baseChangeMap q (quotHom φ t))
    (baseChangeMap_comp_snd q (quotHom φ t)) k

end Reduction

end Deformation.Artin.SectionsSheaf

end

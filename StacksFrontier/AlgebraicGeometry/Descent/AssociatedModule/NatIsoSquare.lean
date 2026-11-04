module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoCoherence

/-!
# The coherence square of Stacks 03DV, read through the composition of left adjoints

`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is the comparison

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`

that Stacks 03DV leaves implicit, and
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_conjugate` reduces its
compatibility with composition of objects of the big fppf site to the corresponding identity
between the mates.  This file analyses that identity.

Every comparison in the square is an isomorphism between left adjoints, and the three-step
composite that the square equates with the one-step comparison is exactly the pentagon of
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`: the pullback of modules on schemes along
the structure morphism of `T`, the pullback along the structure morphism of `T'` over the scheme
of `T`, and the associated-module functor of the big fppf site of the scheme of `T'` are three
composable left adjoints, and the three comparisons the square is built from are the comparisons
`CategoryTheory.Adjunction.leftAdjointCompIso` associates to their mates.

## Main results

* `Stacks.Mates.leftAdjointCompIso_conjugateIsoEquiv_symm`: **an isomorphism between a composite
  of two left adjoints and a left adjoint is the comparison that
  `CategoryTheory.Adjunction.leftAdjointCompIso` builds from its own mate.**  This is what makes
  `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` applicable to isomorphisms that were not
  constructed by `CategoryTheory.Adjunction.leftAdjointCompIso` in the first place.
* `Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom` and
  `Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight`: **the mate of the canonical
  comparison of two left adjoints of functors that are only isomorphic is that isomorphism.**
  Every comparison in the square is built as
  `CategoryTheory.Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)`, and no mate of such a
  comparison was recorded; this computes it.
* `Stacks.Mates.trans_assoc_of_conjugate`: **the pentagon for three composable left adjoints
  follows from the pentagon for their mates.**
* `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackCongr` and
  `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackSquareIso`: **the mates of the two transports
  of a pullback of sheaves of modules are the corresponding transports of the pushforward**,
  which are the identity on sections.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon`: **the
  comparison of Stacks 03DV is compatible with composition of objects of the big fppf site**,
  granted the pentagon for the mates of its factors.

## Implementation notes

Nothing here carries a `stacks` attribute: the comparison this file is about is a step
Stacks 03DV leaves implicit and carries no tag of its own.

The square is still not unconditional, and exactly one of the mates that
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` asks for is
not available.  Of the four entries of its pentagon:

* the mate of the contraction of the iterated pullback of modules on schemes is
  `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` together with
  `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackCongr`;
* the mate of `AlgebraicGeometry.BigFppfOver.associatedModuleObjIso`, through which
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` factors, is
  `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackSquareIso`;
* the mate of the factor of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso`
  coming from the reindexing equivalence of Stacks 06WI is the identity, by
  `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom`: that factor compares two left
  adjoints of one and the same functor, the twist of
  `Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight` being trivial there;
* the mate of `AlgebraicGeometry.BigFppfOver.objRestrictComp` is the one that is missing.  It has
  to be taken with respect to `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`,
  where restriction to an object is the *left* adjoint of `SheafOfModules.overPullback`, so the
  mate of `Stacks.SheafOfModules.overMapCompIso` — a comparison of pushforwards — is a
  comparison of `SheafOfModules.overPullback`s induced by `CategoryTheory.Over.pullbackComp`, and
  no such comparison exists.  With respect to
  `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` the same obstruction moves to the other
  three entries, whose mates are then not the identity.

Nothing here unfolds `AlgebraicGeometry.BigFppfOver.objRestrict`, which is a reducible
abbreviation whose body is the structure sheaf of the big fppf site: every statement is at the
level of functors and adjunctions, and
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` is proved by
a single application of `Stacks.Mates.trans_assoc_of_conjugate`.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ v₁ v₂ v₃ v₄ w u₀ u₁ u₂ u₃ u₄ v u

namespace Stacks.Mates

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- **An isomorphism between a composite of two left adjoints and a left adjoint is the
comparison that `CategoryTheory.Adjunction.leftAdjointCompIso` builds from its own mate.**
Conjugation is a bijection between isomorphisms of left adjoints and isomorphisms of the
corresponding right adjoints, and `CategoryTheory.Adjunction.leftAdjointCompIso` is its inverse;
so every isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂` between left adjoints is in its image, namely at its own
mate.

This is what makes the pentagon `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` usable for
isomorphisms that were not built by `CategoryTheory.Adjunction.leftAdjointCompIso`. -/
public theorem leftAdjointCompIso_conjugateIsoEquiv_symm
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (α : F₀₁ ⋙ F₁₂ ≅ F₀₂) :
    Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂
        (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂) α).symm = α := by
  dsimp only [Adjunction.leftAdjointCompIso]
  rw [Iso.symm_symm_eq, Equiv.symm_apply_apply]

/-- **The mate of the canonical comparison of two left adjoints of functors that are only
isomorphic.**  Let `L₁ ⊣ R` and `L₂ ⊣ R₂` be adjunctions and let `e : R₂ ≅ R`.  Transporting the
second adjunction along `e` makes `L₁` and `L₂` left adjoints of one and the same functor, so
`CategoryTheory.Adjunction.leftAdjointUniq` compares them; the mate of that comparison with
respect to the two *untwisted* adjunctions is `e` itself.

`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom` is the case `e = Iso.refl`.  The
general case is what computes the mate of every comparison built as
`CategoryTheory.Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)` — the shape of
`SheafOfModules.pullbackSquareIso`, of `Stacks.SheafOfModules.pullbackCongr` and of
`AlgebraicGeometry.BigFppfOver.associatedModulePullbackIso`, none of whose mates was recorded.
The proof is the naturality of `e` followed by the triangle identity for the second
adjunction. -/
public theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    {L₁ L₂ : C₀ ⥤ C₁} {R R₂ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R) :
    conjugateEquiv adj₂ adj₁
        (Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)).hom = e.hom := by
  ext d
  simp only [conjugateEquiv_apply_app]
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc,
    adj₂.right_triangle_components, Category.id_comp]

/-- **The mate of the canonical comparison of two left adjoints of isomorphic functors, as an
isomorphism.**  This is `Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom` read
through `CategoryTheory.conjugateIsoEquiv`: the comparison of left adjoints produced by
transporting one adjunction along `e : R₂ ≅ R` has mate exactly `e`. -/
public theorem conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight
    {L₁ L₂ : C₀ ⥤ C₁} {R R₂ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R) :
    conjugateIsoEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)) = e :=
  Iso.ext (by
    simpa using conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom adj₁ adj₂ e)

section Pentagon

variable {C₃ : Type u₃} [Category.{v₃} C₃]

/-- **The pentagon for three composable left adjoints follows from the pentagon for their
mates.**  Let `F₀₁`, `F₁₂`, `F₂₃` be three composable left adjoints, let `F₀₂`, `F₁₃`, `F₀₃` be
left adjoints standing for the three remaining composites, and let `α₀₁₂`, `α₁₂₃`, `α₀₁₃`, `α₀₂₃`
be the four comparison isomorphisms.  If the mates of the four comparisons satisfy the pentagon
for the right adjoints, then the comparisons satisfy the pentagon for the left adjoints — in the
orientation that solves for the long composite `α₀₂₃`.

This is `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` made applicable to arbitrary
comparison isomorphisms by `Stacks.Mates.leftAdjointCompIso_conjugateIsoEquiv_symm`, and
reoriented: the identity it concludes is the one asserting that going round the square the long
way agrees with the short way. -/
public theorem trans_assoc_of_conjugate
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃}
    {F₀₃ : C₀ ⥤ C₃} {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀}
    {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)
    (α₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (α₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (α₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (α₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (h : Functor.isoWhiskerLeft G₃₂ (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂) α₀₁₂).symm ≪≫
          (conjugateIsoEquiv adj₀₃ (adj₀₂.comp adj₂₃) α₀₂₃).symm =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
              (conjugateIsoEquiv adj₁₃ (adj₁₂.comp adj₂₃) α₁₂₃).symm G₁₀ ≪≫
            (conjugateIsoEquiv adj₀₃ (adj₀₁.comp adj₁₃) α₀₁₃).symm) :
    (Functor.isoWhiskerRight α₀₁₂ F₂₃).symm ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft F₀₁ α₁₂₃ ≪≫ α₀₁₃ = α₀₂₃ := by
  have key := Adjunction.leftAdjointCompIso_assoc adj₀₁ adj₁₂ adj₂₃ adj₀₂ adj₁₃ adj₀₃ _ _ _ _ h
  simp only [leftAdjointCompIso_conjugateIsoEquiv_symm] at key
  rw [key]
  simp

end Pentagon

end Stacks.Mates

namespace Stacks.SheafOfModules

section Congr

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {J₁ : GrothendieckTopology C₁} {K₁ : GrothendieckTopology D₁} {F : C₁ ⥤ D₁}
  {S₁ : Sheaf J₁ RingCat.{w}} {R₁ : Sheaf K₁ RingCat.{w}} [Functor.IsContinuous F J₁ K₁]

/-- **The mate of `Stacks.SheafOfModules.pullbackCongr` is
`SheafOfModules.pushforwardCongr`.**  Transport of the pullback of sheaves of modules along an
equality of morphisms of sheaves of rings is defined through the uniqueness of a left adjoint,
so no computation of its sections is available; but its mate is the transport of the pushforward,
which is the identity on sections. -/
public theorem conjugateIsoEquiv_pullbackCongr
    {φ ψ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₁ K₁).obj R₁}
    [(SheafOfModules.pushforward.{w} φ).IsRightAdjoint]
    [(SheafOfModules.pushforward.{w} ψ).IsRightAdjoint] (hφψ : φ = ψ) :
    conjugateIsoEquiv (SheafOfModules.pullbackPushforwardAdjunction.{w} ψ)
        (SheafOfModules.pullbackPushforwardAdjunction.{w} φ)
        (Stacks.SheafOfModules.pullbackCongr.{w} hφψ) =
      SheafOfModules.pushforwardCongr.{w} hφψ.symm :=
  Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight _ _ _

end Congr

section Square

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {a : C ⥤ C'} {b : C' ⥤ D'} {c : C ⥤ D} {d : D ⥤ D'}
  [a.IsContinuous J J'] [b.IsContinuous J' K'] [c.IsContinuous J K] [d.IsContinuous K K']
  [(a ⋙ b).IsContinuous J K'] [(c ⋙ d).IsContinuous J K']
  {RC : Sheaf J RingCat.{u}} {RC' : Sheaf J' RingCat.{u}}
  {RD : Sheaf K RingCat.{u}} {RD' : Sheaf K' RingCat.{u}}
  (φa : RC ⟶ (a.sheafPushforwardContinuous RingCat.{u} J J').obj RC')
  (φb : RC' ⟶ (b.sheafPushforwardContinuous RingCat.{u} J' K').obj RD')
  (φc : RC ⟶ (c.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
  (φd : RD ⟶ (d.sheafPushforwardContinuous RingCat.{u} K K').obj RD')
  [(SheafOfModules.pushforward.{v} φa).IsRightAdjoint]
  [(SheafOfModules.pushforward.{v} φb).IsRightAdjoint]
  [(SheafOfModules.pushforward.{v} φc).IsRightAdjoint]
  [(SheafOfModules.pushforward.{v} φd).IsRightAdjoint]

/-- **The mate of `SheafOfModules.pullbackSquareIso` is the comparison of pushforwards it was
built from.**  Stacks 03D8 for a square compares the two composite pullbacks by exhibiting both
as left adjoints of the two composite pushforwards, which the datum of the square identifies;
the mate of the comparison, with respect to the two composite pullback-pushforward adjunctions,
is that identification.

This is the computation that was missing for
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso`, through which
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` factors: the right-hand side is
a composite of comparisons of *pushforwards* of sheaves of modules, and those are the identity on
sections. -/
public theorem conjugateIsoEquiv_pullbackSquareIso (e : a ⋙ b ≅ c ⋙ d)
    (he : SheafOfModules.comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      SheafOfModules.comparisonComp φa φb) :
    conjugateIsoEquiv
        ((SheafOfModules.pullbackPushforwardAdjunction.{v} φc).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{v} φd))
        ((SheafOfModules.pullbackPushforwardAdjunction.{v} φa).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{v} φb))
        (SheafOfModules.pullbackSquareIso.{v} φa φb φc φd e he) =
      SheafOfModules.pushforwardComp.{v} φc φd ≪≫
        SheafOfModules.pushforwardCongr₂.{v} _ e he ≪≫
          (SheafOfModules.pushforwardComp.{v} φa φb).symm :=
  Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight _ _ _

end Square

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of Stacks 03DV is compatible with composition of objects of the big fppf
site**, granted the pentagon for the mates of its three factors.

This is `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_conjugate` with
its hypothesis taken apart.  There the hypothesis was a single identity between the mates of the
two whole composites; here it is the pentagon of `Stacks.Mates.trans_assoc_of_conjugate`, whose
four entries are the mates of the four comparisons separately:

* the mate of the contraction of the iterated pullback of modules on schemes, which
  `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` computes;
* the mate of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at the object
  `g` of the big fppf category over the scheme of `T`;
* the mate of the three-step route through `T`, which is the mate of
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at `T` composed with that of
  `AlgebraicGeometry.BigFppfOver.objRestrictComp`;
* the mate of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at `T'`.

The two adjunctions for restriction to an object are taken as arguments, as in
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_ext`, because the mates depend
on them; `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` and
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` are the two available
choices. -/
public theorem associatedModuleObjRestrictNatIso_comp_of_pentagon
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    {G' : SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T') (contains_objScheme B S hS T')) ⥤
      SheafOfModules.{u} (structureSheaf B S hS)} (adj' : objRestrict B S hS T' ⊣ G')
    {GU : SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T') (contains_objScheme B S hS T')) ⥤
      SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T))}
    (adjU : objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left) ⊣ GU)
    (h : Functor.isoWhiskerLeft
            (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
            (conjugateIsoEquiv
              (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T'))
              ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
                (Scheme.Modules.pullbackPushforwardAdjunction
                  (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
                    (Over.mk g.left))))
              (Scheme.Modules.pullbackComp
                  (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
                    (Over.mk g.left))
                  (objHom B S hS T) ≪≫
                Scheme.Modules.pullbackCongr (objHom_comp B S hS g))).symm ≪≫
          (conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj')
            ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T')).comp
              (associatedModuleAdjunction B (objScheme B S hS T')
                (contains_objScheme B S hS T')))
            (associatedModuleObjRestrictNatIso B S hS T')).symm =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
              (conjugateIsoEquiv
                ((associatedModuleAdjunction B (objScheme B S hS T)
                    (contains_objScheme B S hS T)).comp adjU)
                ((Scheme.Modules.pullbackPushforwardAdjunction
                    (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
                      (Over.mk g.left))).comp
                  (associatedModuleAdjunction B (objScheme B S hS T')
                    (contains_objScheme B S hS T')))
                (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
                  (contains_objScheme B S hS T) (Over.mk g.left))).symm
              (Scheme.Modules.pushforward (objHom B S hS T)) ≪≫
            (conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj')
              ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
                ((associatedModuleAdjunction B (objScheme B S hS T)
                    (contains_objScheme B S hS T)).comp adjU))
              ((Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B S hS T) _ ≪≫
                  Functor.associator _ _ _ ≪≫
                    Functor.isoWhiskerLeft _ (objRestrictComp B S hS g))).symm) :
    (Functor.isoWhiskerRight
          (Scheme.Modules.pullbackComp
              (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
              (objHom B S hS T) ≪≫
            Scheme.Modules.pullbackCongr (objHom_comp B S hS g))
          (associatedModule B (objScheme B S hS T') (contains_objScheme B S hS T'))).symm ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _
              (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
                (contains_objScheme B S hS T) (Over.mk g.left)) ≪≫
            (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B S hS T) _ ≪≫
                Functor.associator _ _ _ ≪≫
                  Functor.isoWhiskerLeft _ (objRestrictComp B S hS g) =
      associatedModuleObjRestrictNatIso B S hS T' :=
  Stacks.Mates.trans_assoc_of_conjugate _ _ _ _ _ _ _ _ _ _ h

end AlgebraicGeometry.BigFppfOver

end

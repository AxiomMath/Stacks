module

public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Triviality of a sheaf of modules under pullback, and the faces of a fibre product

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes with sections `σ` of `f` and `τ` of
`g`, let `P = X ×_S Y`, let `p : P ⟶ S` be the structure morphism, and let `L` be a sheaf of
modules on `P`. [Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3) asserts that `L`
is trivial over some open neighbourhood of a point `s ∈ S` as soon as `L` is invertible, `f`
and `g` are flat, proper and of finite presentation with universally invariant structure
sheaf, and the three restrictions of `L` to the face `1 × τ : X ⟶ P`, to the face
`σ × 1 : Y ⟶ P` and to the fibre `P ×_S Spec κ(s)` are trivial.

This file proves the statements around that tag which follow from the fact that pullback of
sheaves of modules carries a trivial module to a trivial module: `f^* 𝒪_Y ≅ 𝒪_X` for every
morphism of ringed spaces, which is `RingedSpaceModuleAdjunction.modulePullbackUnitIso`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback`: the pullback of a trivial sheaf
  of modules along a morphism of ringed spaces is trivial. Its scheme spelling is
  `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme`.
* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_of_comp` and its scheme spelling
  `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp`: if the pullback
  of `L` along `b` is trivial and `a ≫ b = c`, then the pullback of `L` along `c` is trivial.
* `AlgebraicGeometry.SheafOfModules.isTrivial_faces_and_fiber_of_isTrivial`: the three
  triviality hypotheses of Tag 0BF3, on the two faces and on the fibre over `s`, are implied by
  triviality of `L` on all of `X ×_S Y`, with no hypothesis on `f` and `g`.
* `AlgebraicGeometry.SheafOfModules.exists_isTrivial_on_open_of_isTrivial`: a globally trivial
  `L` satisfies the conclusion of Tag 0BF3, with `U = ⊤`.
* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_fst_ι_of_le`: the conclusion of
  Tag 0BF3 is monotone: if `L` is trivial over `P ×_S U` and `V ≤ U`, then `L` is trivial over
  `P ×_S V`.
* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_sectionLift_of_isTrivial_face`:
  the first face hypothesis of Tag 0BF3 forces the restriction of `L` along the section
  `(σ, τ) : S ⟶ X ×_S Y` to be trivial.

## Implementation notes

Triviality is `AlgebraicGeometry.SheafOfModules.IsTrivial`, which is `Nonempty` of an
isomorphism with the structure sheaf viewed as a module over itself. Pullback is
`RingedSpaceModuleAdjunction.modulePullback`, which consumes a morphism of ringed spaces; a
morphism of schemes is fed to it through `Scheme.Hom.toLRSHom` and
`LocallyRingedSpace.Hom.toShHom`. The sheaf of rings indexing the modules on a scheme `X` is
`structureSheafRing X.toRingedSpace`, which is the same term as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` at `X.presheaf`; the two spellings
are interchangeable without a cast.

`isTrivial_modulePullback_of_comp` takes the factorisation `a ≫ b = c` as a hypothesis rather
than pulling it apart, so that callers never have to produce an `eqToIso` between pullback
functors: the equation is eliminated by `subst` inside a proof of a `Prop`, and the transport
is carried by `RingedSpaceModuleAdjunction.modulePullbackComp`.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- **Pullback preserves triviality.** The pullback of a sheaf of modules isomorphic to the
structure sheaf is isomorphic to the structure sheaf, for every morphism of ringed spaces. -/
theorem isTrivial_modulePullback {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    {L : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (hL : Nonempty (L ≅ _root_.SheafOfModules.unit (structureSheafRing Y))) :
    Nonempty ((modulePullback h).obj L ≅ _root_.SheafOfModules.unit (structureSheafRing X)) :=
  ⟨(modulePullback h).mapIso hL.some ≪≫
    RingedSpaceModuleAdjunction.modulePullbackUnitIso h⟩

/-- **Triviality of a restriction passes to a further restriction.** If `c` factors as
`a ≫ b` and the pullback of `L` along `b` is trivial, then so is the pullback of `L` along `c`. -/
theorem isTrivial_modulePullback_of_comp {X Y Z : RingedSpace.{u, u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c)
    {L : _root_.SheafOfModules.{u} (structureSheafRing Z)}
    (hL : Nonempty ((modulePullback b).obj L ≅ _root_.SheafOfModules.unit (structureSheafRing Y))) :
    Nonempty ((modulePullback c).obj L ≅ _root_.SheafOfModules.unit (structureSheafRing X)) := by
  subst hc
  exact ⟨(RingedSpaceModuleAdjunction.modulePullbackComp a b).app L ≪≫
    (isTrivial_modulePullback a hL).some⟩

/-- `isTrivial_modulePullback` for a morphism of schemes, in the spelling of `IsTrivial` that
names the structure sheaf by the scheme's presheaf of rings. -/
theorem isTrivial_modulePullback_scheme {X Y : Scheme.{u}} (h : X ⟶ Y)
    {L : _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)}
    (hL : IsTrivial Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L) :
    IsTrivial X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
      ((modulePullback h.toLRSHom.toShHom).obj L) :=
  isTrivial_modulePullback _ hL

/-- `isTrivial_modulePullback_of_comp` for morphisms of schemes. -/
theorem isTrivial_modulePullback_scheme_of_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c)
    {L : _root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)}
    (hL : IsTrivial Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf)
      ((modulePullback b.toLRSHom.toShHom).obj L)) :
    IsTrivial X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
      ((modulePullback c.toLRSHom.toShHom).obj L) :=
  isTrivial_modulePullback_of_comp a.toLRSHom.toShHom b.toLRSHom.toShHom c.toLRSHom.toShHom
    (by rw [← hc]; rfl) hL

section Faces

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The three triviality hypotheses of Tag 0BF3 are necessary.** If `L` is trivial on all of
`X ×_S Y` then its restrictions to the face `1 × τ`, to the face `σ × 1` and to the fibre over
`s` are all trivial. The three conclusions are stated exactly as that tag states its
hypotheses. -/
theorem isTrivial_faces_and_fiber_of_isTrivial
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S) (s : S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    (hL : IsTrivial (pullback f g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback f g).IsSheaf) L) :
    (let i : X ⟶ pullback f g :=
        pullback.lift (𝟙 X) (f ≫ τ)
          (by simp only [Category.id_comp, Category.assoc, hτ, Category.comp_id]);
      IsTrivial X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L)) ∧
    (let i : Y ⟶ pullback f g :=
        pullback.lift (g ≫ σ) (𝟙 Y)
          (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp]);
      IsTrivial Y.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L)) ∧
    (let P := pullback f g;
      let p : P ⟶ S := pullback.fst f g ≫ f;
      let W := pullback p (S.fromSpecResidueField s);
      IsTrivial W.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
        ((modulePullback
          (pullback.fst p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj L)) :=
  ⟨isTrivial_modulePullback_scheme _ hL, isTrivial_modulePullback_scheme _ hL,
    isTrivial_modulePullback_scheme _ hL⟩

/-- **The conclusion of Tag 0BF3 holds for a globally trivial module**, with `U = ⊤`. -/
theorem exists_isTrivial_on_open_of_isTrivial (s : S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    (hL : IsTrivial (pullback f g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback f g).IsSheaf) L) :
    ∃ U : S.Opens, s ∈ U ∧
      (let P := pullback f g;
        let p : P ⟶ S := pullback.fst f g ≫ f;
        let W := pullback p U.ι;
        IsTrivial W.presheaf
          (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
          ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) :=
  ⟨⊤, trivial, isTrivial_modulePullback_scheme _ hL⟩

/-- **The first face hypothesis of Tag 0BF3 trivialises `L` along the section `(σ, τ)`.** If the
pullback of `L` along the face `1 × τ : X ⟶ X ×_S Y` is trivial, then so is its pullback along
the section `S ⟶ X ×_S Y` with components `σ` and `τ`. -/
theorem isTrivial_modulePullback_sectionLift_of_isTrivial_face
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    (hface :
      let i : X ⟶ pullback f g :=
        pullback.lift (𝟙 X) (f ≫ τ)
          (by simp only [Category.id_comp, Category.assoc, hτ, Category.comp_id])
      IsTrivial X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L)) :
    IsTrivial S.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) S.IsSheaf)
      ((modulePullback
        (pullback.lift σ τ (by rw [hσ, hτ])).toLRSHom.toShHom).obj L) :=
  isTrivial_modulePullback_scheme_of_comp σ _ _
    (pullback.hom_ext
      (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hσ,
        Category.id_comp]))
    hface

end Faces

/-- **The conclusion of Tag 0BF3 is monotone in the open.** If the restriction of `L` to
`P ×_S U` is trivial and `V ≤ U`, then the restriction of `L` to `P ×_S V` is trivial. -/
theorem isTrivial_modulePullback_fst_ι_of_le {S P : Scheme.{u}} (p : P ⟶ S)
    {U V : S.Opens} (hVU : V ≤ U)
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (h : IsTrivial (pullback p U.ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p U.ι).IsSheaf)
      ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) :
    IsTrivial (pullback p V.ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p V.ι).IsSheaf)
      ((modulePullback (pullback.fst p V.ι).toLRSHom.toShHom).obj L) :=
  isTrivial_modulePullback_scheme_of_comp
    (pullback.lift (pullback.fst p V.ι) (pullback.snd p V.ι ≫ S.homOfLE hVU)
      (by rw [pullback.condition, Category.assoc, Scheme.homOfLE_ι]))
    (pullback.fst p U.ι) (pullback.fst p V.ι) (by rw [pullback.lift_fst]) h

end AlgebraicGeometry.SheafOfModules

end

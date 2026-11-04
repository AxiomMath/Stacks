module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Additive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of rings on the big fpqc site

Let `S` be a scheme. The additive group scheme `𝐆_{a,S} = 𝐀¹_S` over `S` represents global
regular functions: a morphism of `S`-schemes `T ⟶ 𝐆_{a,S}` is the same thing as a global
section of `𝒪_T`. The resulting presheaf of sets on the schemes over `S` therefore satisfies
the sheaf condition for the fpqc topology, because the fpqc topology is subcanonical. Global
sections of the structure sheaf form a *ring*, so the same presheaf refines to a functor
`𝒪 : (Sch/S)ᵒᵖ ⥤ Rings`, `T/S ↦ Γ(T, 𝒪_T)`, and this refinement again satisfies the fpqc sheaf
condition.

## Main definitions

* `AlgebraicGeometry.Scheme.bigStructurePresheaf`: the functor `𝒪 : (Sch/S)ᵒᵖ ⥤ CommRingCat`
  sending an `S`-scheme `T` to the ring `Γ(T, 𝒪_T)`, with pullback of functions as its
  restriction maps.
* `AlgebraicGeometry.Scheme.bigStructureSheaf`: the same data packaged as a sheaf of rings for
  the fpqc topology on the schemes over `S`.
* `AlgebraicGeometry.bigStructurePresheafRepresentableBy`: the additive group scheme over `S`
  represents the underlying presheaf of sets of `𝒪`.

## Main results

* `AlgebraicGeometry.additiveGroupBaseChangeYonedaIsoBigStructurePresheaf`: the natural
  bijection `Mor_S(T, 𝐆_{a,S}) ≃ Γ(T, 𝒪_T)`, as an isomorphism of presheaves of sets on the
  schemes over `S`.
* `AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_Γ`: the ring-valued global-sections functor on
  *all* schemes is a sheaf for the fpqc topology.
* `AlgebraicGeometry.isSheaf_fpqc_bigStructurePresheaf_forget`: the presheaf of sets
  `T/S ↦ Γ(T, 𝒪_T)` satisfies the fpqc sheaf condition.
* `AlgebraicGeometry.Scheme.isSheaf_fpqc_bigStructurePresheaf`: the presheaf of *rings*
  `T/S ↦ Γ(T, 𝒪_T)` satisfies the fpqc sheaf condition.

## Implementation notes

*The fpqc sheaf condition for a ring-valued presheaf is proved pointwise, not by forgetting the
ring structure.* Mathlib's `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` reduces the
sheaf condition for an `A`-valued presheaf to the one for `A`'s underlying presheaf of sets,
but only for `A` whose morphisms live in the universe `max v₁ u₁` of the site; on
`Scheme.{u}`-schemes over `S` that universe is `u + 1`, whereas `AlgebraicGeometry.Scheme.Γ`
takes values in `CommRingCat.{u}`, so it does not apply here. Instead the definition of
`CategoryTheory.Presheaf.IsSheaf` is used directly: it asks that `Hom(E, 𝒪 -)` be a sheaf of
types for every ring `E`, and `Hom(E, Γ(T, 𝒪_T))` is naturally `Mor(T, Spec E)` by the
`Γ`-`Spec` adjunction, hence representable, hence a sheaf by subcanonicality. This argument is
insensitive to `S`, so it is carried out on all schemes once in
`AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_Γ` and then restricted along
`CategoryTheory.Over.forget`, which is continuous for the localized topology.

*The base change is handled by a general slice transport.*
`CategoryTheory.Functor.RepresentableBy.overPullback` says that a presheaf of types represented
by `X` is, after restriction along `CategoryTheory.Over.forget S`, represented by `X ×_Z S` over
`S`, whenever `Z` is terminal. Applied to the integral model it turns Stacks 022V's
`AlgebraicGeometry.globalSectionsRepresentableBy` into the representability of `𝒪` by
`AlgebraicGeometry.additiveGroupBaseChange`, so no second computation with the affine line is
needed.

## References

* [Stacks Project, Tag 03O5](https://stacks.math.columbia.edu/tag/03O5)
* [Stacks Project, Tag 03O4](https://stacks.math.columbia.edu/tag/03O4)
* [Stacks Project, Tag 022V](https://stacks.math.columbia.edu/tag/022V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A presheaf of types on `C` represented by `X` is, after restriction along
`CategoryTheory.Over.forget S`, represented by the base change `X ×_Z S` of `X` to `S`, viewed
over `S` by its second projection, provided `Z` is a terminal object: a morphism `T ⟶ X ×_Z S`
of objects over `S` is the same thing as a morphism `T ⟶ X`, since the compatibility over `Z`
is automatic. -/
@[sga "3 I 1.6.1" "partial"]
noncomputable def Functor.RepresentableBy.overPullback {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : F.RepresentableBy X) {Z S : C} (hZ : IsTerminal Z) (p : X ⟶ Z) (q : S ⟶ Z)
    [HasPullback p q] :
    ((Over.forget S).op ⋙ F).RepresentableBy (Over.mk (pullback.snd p q)) where
  homEquiv {T} :=
    { toFun f := e.homEquiv (f.left ≫ pullback.fst p q)
      invFun x :=
        Over.homMk (pullback.lift (e.homEquiv.symm x) T.hom (hZ.hom_ext _ _))
          (pullback.lift_snd _ _ _)
      left_inv f := by
        refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
        · simp only [Over.homMk_left, pullback.lift_fst, Equiv.symm_apply_apply]
        · simp only [Over.homMk_left, pullback.lift_snd]
          exact (Over.w f).symm
      right_inv x := by
        simp only [Over.homMk_left, pullback.lift_fst, Equiv.apply_symm_apply] }
  homEquiv_comp {T T'} f g := by
    simp only [Equiv.coe_fn_mk, Over.comp_left, Category.assoc]
    exact e.homEquiv_comp _ _

end CategoryTheory

namespace AlgebraicGeometry

/-- The ring of homomorphisms out of a fixed ring into global sections is represented by the
spectrum of that ring: a ring map `E ⟶ Γ(T, 𝒪_T)` is the same thing as a morphism of schemes
`T ⟶ Spec E`. This is the `Γ`-`Spec` adjunction read as a representability statement. -/
noncomputable def coyonedaCompΓRepresentableBy (E : CommRingCat.{u}) :
    (Scheme.Γ.{u} ⋙ coyoneda.obj (op E)).RepresentableBy (Spec E) where
  homEquiv {T} := (ΓSpec.adjunction.homEquiv T (op E)).symm.trans (opEquiv _ _)
  homEquiv_comp {T T'} f g := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm]
    rfl

/-- **The ring-valued global-sections functor on schemes is a sheaf for the fpqc topology.**
By the definition of the sheaf condition for a presheaf with values in an arbitrary category,
it suffices that `Hom(E, Γ(-, 𝒪))` be a sheaf of types for every ring `E`; that presheaf is
represented by `Spec E`, and the fpqc topology is subcanonical. -/
@[sga "4 VII 4.2" "special case"]
theorem Scheme.isSheaf_fpqcTopology_Γ :
    Presheaf.IsSheaf Scheme.fpqcTopology.{u} Scheme.Γ.{u} := fun E ↦
  have : (Scheme.Γ.{u} ⋙ coyoneda.obj (op E)).IsRepresentable :=
    (coyonedaCompΓRepresentableBy E).isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The structure presheaf `𝒪` of the big site of a scheme `S`: it sends an `S`-scheme `T` to
the ring `Γ(T, 𝒪_T)` of global regular functions on `T`, and a morphism of `S`-schemes to
pullback of functions along it. -/
noncomputable abbrev Scheme.bigStructurePresheaf (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ.{u}

/-- **Stacks 03O5.** The additive group scheme `𝐆_{a,S}` over `S` represents the underlying
presheaf of sets of the structure presheaf of the big site of `S`: a morphism of `S`-schemes
`T ⟶ 𝐆_{a,S}` is the same thing as a global section of `𝒪_T`.

This is Stacks 022V's representability of global sections by the affine line over the integers,
transported to the schemes over `S` along the base change defining `𝐆_{a,S}`. -/
@[ega "I 3.3.15" "more general", ega "II 1.7.12" "more general", sga "3 I 4.3.1" "more general"]
noncomputable def bigStructurePresheafRepresentableBy (S : Scheme.{u}) :
    (Scheme.bigStructurePresheaf S ⋙ forget CommRingCat).RepresentableBy
      (Scheme.asOver (additiveGroupBaseChange S) S) :=
  globalSectionsRepresentableBy.overPullback specULiftZIsTerminal
    (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)

/-- **Stacks 03O5.** The natural bijection `Mor_S(T, 𝐆_{a,S}) ≃ Γ(T, 𝒪_T)`, as an isomorphism
of presheaves of sets on the schemes over `S`: the presheaf represented by the additive group
scheme over `S` is the presheaf of global regular functions. -/
@[stacks 03O5 "functor of points"]
noncomputable def additiveGroupBaseChangeYonedaIsoBigStructurePresheaf (S : Scheme.{u}) :
    yoneda.obj (Scheme.asOver (additiveGroupBaseChange S) S) ≅
      Scheme.bigStructurePresheaf S ⋙ forget CommRingCat :=
  Functor.representableByEquiv (bigStructurePresheafRepresentableBy S)

/-- **Stacks 03O5.** The presheaf of sets `T/S ↦ Γ(T, 𝒪_T)` on the schemes over `S` satisfies
the sheaf condition for the fpqc topology: it is represented by the additive group scheme over
`S`, and the fpqc topology on the schemes over `S` is subcanonical. -/
@[stacks 03O5 "fpqc sheaf of sets"]
theorem isSheaf_fpqc_bigStructurePresheaf_forget (S : Scheme.{u}) :
    Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (Scheme.bigStructurePresheaf S ⋙ forget CommRingCat) :=
  have : (Scheme.bigStructurePresheaf S ⋙ forget CommRingCat).IsRepresentable :=
    (bigStructurePresheafRepresentableBy S).isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- **Stacks 03O5.** The presheaf of *rings* `𝒪 : (Sch/S)ᵒᵖ ⥤ Rings`, `T/S ↦ Γ(T, 𝒪_T)`,
satisfies the sheaf condition for the fpqc topology on the schemes over `S`.

This is `AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_Γ` restricted along the forgetful functor
`Sch/S ⥤ Sch`, which is continuous from the localized fpqc topology to the fpqc topology. -/
@[stacks 03O5 "fpqc sheaf of rings", sga "4 VII 4.2" "special case"]
theorem Scheme.isSheaf_fpqc_bigStructurePresheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (Scheme.bigStructurePresheaf S) :=
  (Over.forget S).op_comp_isSheaf_of_isSheaf _ _ _ Scheme.isSheaf_fpqcTopology_Γ

/-- The structure sheaf of rings on the big fpqc site of a scheme `S`. -/
noncomputable def Scheme.bigStructureSheaf (S : Scheme.{u}) :
    Sheaf (Scheme.fpqcTopology.{u}.over S) CommRingCat.{u} :=
  ⟨Scheme.bigStructurePresheaf S, Scheme.isSheaf_fpqc_bigStructurePresheaf S⟩

end AlgebraicGeometry

end

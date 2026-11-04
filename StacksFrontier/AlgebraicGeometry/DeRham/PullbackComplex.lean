module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DeRhamOrderOne
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham complex of an inverse image, as a complex of modules

Let `f : X ⟶ Y` be a morphism of schemes and `g : Y ⟶ S` the structure morphism of the target.
The relative de Rham complex `Ω^•_{Y/S}` is a complex of `g^{-1}𝒪_S`-modules on `Y` and
`Ω^•_{X/S}` is a complex of `(f∘g)^{-1}𝒪_S`-modules on `X`; pulling the first back along the
morphism of ringed spaces `(X, (f∘g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` gives the canonical

`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}`

as a morphism of complexes of `(f∘g)^{-1}𝒪_S`-modules.

`StacksFrontier.AlgebraicGeometry.DeRham.Functoriality` has the canonical map of de Rham complexes
only in abelian sheaves, because the de Rham differential is not `𝒪`-linear and a map of
complexes of modules needs the base-change morphism of ring sheaves of the square; that morphism
is `Stacks.DeRhamSmooth.relativeBase`. With it in hand the module-level map is obtained from the
graded-algebra homomorphism of Tag 07HX by restriction of scalars and adjunction: a map out of a
pullback is a map into a pushforward, so the `𝒪_Y`-linear `Ω^p_{Y/S} ⟶ f_*Ω^p_{X/S}` becomes the
`(f∘g)^{-1}𝒪_S`-linear map wanted once its coefficients are restricted along
`g^{-1}𝒪_S ⟶ 𝒪_Y`.

## Main definitions

* `Stacks.DeRhamPullback.relativeBaseSquare`: the commuting square of ringed spaces
  `(X, 𝒪_X) ⟶ (X, (f∘g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` versus
  `(X, 𝒪_X) ⟶ (Y, 𝒪_Y) ⟶ (Y, g^{-1}𝒪_S)`.
* `Stacks.DeRhamPullback.pushforwardSquareIso`: the induced identification of the two composite
  pushforward functors.
* `Stacks.DeRhamPullback.formsPushforward` and `Stacks.DeRhamPullback.deRhamPushforwardChain`:
  the degreewise maps `Ω^p_{Y/S} ⟶ (relativeBase f g)_*Ω^p_{X/S}` of `g^{-1}𝒪_S`-modules, and
  the morphism of complexes they assemble into.
* `Stacks.DeRhamPullback.deRhamPullbackChain`: **`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}`**, the
  adjoint of `deRhamPushforwardChain`.

## Main results

* `Stacks.DeRhamPullback.toInverseImageBase_relativeBase`: the square of ringed spaces commutes.
  Both composites have underlying map that of `f`, and their structure maps agree because both
  transpose, along the inverse-image/direct-image adjunction for `g`, to `(f∘g)^♯`.

## Implementation notes

The structure-map identity of the square is proved in term mode rather than by `rw`: the two
sides mention `(g_* ∘ f_*)` and `(f∘g)_*` of the same sheaf, which are definitionally but not
syntactically equal, so a rewrite leaves a goal that is not type-correct at reducible
transparency.

Every component of `SheafOfModules.pushforwardComp` is the identity on sections, so the only
non-trivial ingredient of `pushforwardSquareIso` is the `eqToIso` of the square; its sectionwise
triviality is extracted by a lemma stated over variable morphisms so that `subst` applies. That
is what reduces the chain-map condition for `deRhamPushforwardChain` to the sectionwise
commutation `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comm` of Tag 07HX.

The adjunction is lifted to complexes by `CategoryTheory.Adjunction.mapHomologicalComplex`, so
`deRhamPullbackChain` is literally the transpose of `deRhamPushforwardChain`; pullback of modules
along a morphism of ringed spaces is additive as a left adjoint, which is what lets it be applied
degreewise to complexes.

**This file is Tag 07HX, not Tag 0FKP.** Stacks Section 07HX records, for a commutative square
of schemes, the two canonical maps of complexes
`f^{-1}Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` and `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}`; `deRhamPullbackChain` is the
first of them, for the square of `f : X ⟶ Y` over `S`, and
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` is the second. It is a *morphism*,
not an isomorphism, and it is built from the graded-algebra homomorphism of Tag 07HX. Tag 0FKP is
a different statement — that for a continuous map of spaces and a homomorphism of sheaves of
rings the inverse image *identifies* `f^{-1}Ω^•_{ℬ/𝒜}` with `Ω^•_{f^{-1}ℬ/f^{-1}𝒜}` — and it is
an input to this map rather than its content; it is proved in
`StacksFrontier.Topology.Sheaves.Modules.DeRhamInverseImage`
(`AlgebraicGeometry.SheafOfModules.inverseImageDeRhamComplexIso`).

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

namespace Stacks.DeRhamPullback

/-- The inverse of the `eqToIso` of an equality of morphisms of ringed spaces acts as the
identity on sections of a pushforward. Stated over variable morphisms so that the equality can
be substituted. -/
theorem eqToIso_pushforward_inv_app_val_app {A B : RingedSpace.{u}} {m m' : A ⟶ B} (h : m = m')
    (M : Modules A) (U : (Opens B.carrier)ᵒᵖ)
    (x : ((_root_.pushforward m').obj M).val.obj U) :
    HEq (((eqToIso (congrArg _root_.pushforward h)).inv.app M).val.app U x) x := by
  subst h
  rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The structure-map identity of the square: the comorphism of `relativeBase f g` followed by
the direct image of the structural map of `f ≫ g` is the structural map of `g` followed by
`f^♯`. Both sides transpose to `(f∘g)^♯`. -/
theorem relativeBase_c_aux :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv S.sheaf
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))).symm
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ g).base).unit.app
          S.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
        (inverseImageStructureMap (f ≫ g)) =
    inverseImageStructureMap g ≫
      (⟨f.c⟩ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) := by
  refine (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
    (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _))
  exact congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv S.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)).symm
    (Scheme.Hom.unit_comp_pushforward_inverseImageStructureMap (f ≫ g))

/-- **The square of ringed spaces commutes**: restricting the coefficients of `𝒪_X` to
`(f∘g)^{-1}𝒪_S` and then projecting to `(Y, g^{-1}𝒪_S)` is `f` followed by restricting the
coefficients of `𝒪_Y` to `g^{-1}𝒪_S`. -/
theorem toInverseImageBase_relativeBase :
    toInverseImageBase (f ≫ g) ≫ relativeBase f g =
      f.toLRSHom.toShHom ≫ toInverseImageBase g :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl
    (heq_of_eq (congrArg (fun t => t.hom) (relativeBase_c_aux f g))))

/-- The identification of the two composite pushforward functors of the square. -/
def pushforwardSquareIso :
    _root_.pushforward (toInverseImageBase (f ≫ g)) ⋙ _root_.pushforward (relativeBase f g) ≅
      _root_.pushforward f.toLRSHom.toShHom ⋙ _root_.pushforward (toInverseImageBase g) :=
  (_root_.pushforwardComp (toInverseImageBase (f ≫ g)) (relativeBase f g)).symm ≪≫
    eqToIso (congrArg _root_.pushforward (toInverseImageBase_relativeBase f g)) ≪≫
    _root_.pushforwardComp f.toLRSHom.toShHom (toInverseImageBase g)

/-- The identification of the two composite pushforwards is the identity on sections. -/
theorem pushforwardSquareIso_inv_val_app (M : Modules X.toRingedSpace) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (((_root_.pushforward f.toLRSHom.toShHom ⋙
      _root_.pushforward (toInverseImageBase g)).obj M)).val.obj U) :
    ((pushforwardSquareIso f g).inv.app M).val.app U x = x :=
  eq_of_heq
    (eqToIso_pushforward_inv_app_val_app (toInverseImageBase_relativeBase f g) M U x)

/-- The degree-`n` component of the canonical homomorphism of Tag 07HX for the square of `f`
over `S`: a map of `𝒪_Y`-modules `Ω^n_{Y/S} ⟶ f_*Ω^n_{X/S}`. -/
abbrev formsPushforwardComponent (n : ℕ) :=
  (Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S)
    ((Category.comp_id (f ≫ g)).symm)).app (n : ℤ)

/-- The degreewise map `Ω^n_{Y/S} ⟶ (relativeBase f g)_*Ω^n_{X/S}` of `g^{-1}𝒪_S`-modules:
the canonical homomorphism of Tag 07HX with its coefficients restricted along
`g^{-1}𝒪_S ⟶ 𝒪_Y`, read through the square. -/
def formsPushforward (n : ℕ) :
    (Scheme.Hom.deRhamComplex g).X n ⟶
      (_root_.pushforward (relativeBase f g)).obj ((Scheme.Hom.deRhamComplex (f ≫ g)).X n) :=
  (_root_.pushforward (toInverseImageBase g)).map (formsPushforwardComponent f g n) ≫
    (pushforwardSquareIso f g).inv.app (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ))

/-- The degreewise maps commute with the arrows of the de Rham complexes. -/
theorem formsPushforwardComponent_comm_d (n : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : ((Scheme.Hom.deRhamAlgebras g).exteriorPower n).val.obj U) :
    ((Scheme.Hom.deRhamComplex (f ≫ g)).d n (n + 1)).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj U)
        ((formsPushforwardComponent f g n).val.app U ω) =
      (formsPushforwardComponent f g (n + 1)).val.app U
        (((Scheme.Hom.deRhamComplex g).d n (n + 1)).val.app U ω) := by
  rw [Scheme.Hom.deRhamComplex_d, Scheme.Hom.deRhamComplex_d]
  exact Scheme.Hom.deRhamFormsPushforwardHom_comm f g (f ≫ g) (𝟙 S) _ n U ω

/-- **The canonical map of de Rham complexes `Ω^•_{Y/S} ⟶ (relativeBase f g)_*Ω^•_{X/S}`**, as a
morphism of complexes of `g^{-1}𝒪_S`-modules. -/
def deRhamPushforwardChain :
    Scheme.Hom.deRhamComplex g ⟶
      ((_root_.pushforward (relativeBase f g)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Scheme.Hom.deRhamComplex (f ≫ g)) where
  f := formsPushforward f g
  comm' := by
    rintro n m rfl
    ext U x
    change ((Scheme.Hom.deRhamComplex (f ≫ g)).d n (n + 1)).val.app
          ((opensMap f.toLRSHom.toShHom).op.obj U)
          (((pushforwardSquareIso f g).inv.app
              (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ))).val.app U
            ((formsPushforwardComponent f g n).val.app U x)) =
        ((pushforwardSquareIso f g).inv.app
            (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((n + 1 : ℕ) : ℤ))).val.app U
          ((formsPushforwardComponent f g (n + 1)).val.app U
            (((Scheme.Hom.deRhamComplex g).d n (n + 1)).val.app U x))
    refine Eq.trans (congrArg (fun z => (((Scheme.Hom.deRhamComplex (f ≫ g)).d n (n + 1)).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj U)) z)
      (pushforwardSquareIso_inv_val_app f g
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)) U
        ((formsPushforwardComponent f g n).val.app U x))) ?_
    exact (formsPushforwardComponent_comm_d f g n U x).trans
      (pushforwardSquareIso_inv_val_app f g
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((n + 1 : ℕ) : ℤ)) U
        ((formsPushforwardComponent f g (n + 1)).val.app U
          (((Scheme.Hom.deRhamComplex g).d n (n + 1)).val.app U x))).symm

/-- Pullback of modules along a morphism of ringed spaces is additive, being a left adjoint, so
it can be applied degreewise to complexes. -/
instance pullback_additive {A B : RingedSpace.{u}} (m : A ⟶ B) : (_root_.pullback m).Additive :=
  (_root_.pullbackPushforwardAdjunction m).left_adjoint_additive

/-- **Stacks Project, Tag 07HX.** The canonical morphism of complexes

`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}`

of `(f∘g)^{-1}𝒪_S`-modules on `X`, adjoint to the canonical map
`Ω^•_{Y/S} ⟶ (relativeBase f g)_*Ω^•_{X/S}` of Tag 07HX read in `g^{-1}𝒪_S`-modules. -/
@[stacks 07HX "the canonical map `f⁻¹Ω^•_{Y/S} ⟶ Ω^•_{X/S}` of a morphism of schemes over `S`, \
read in complexes of `(f∘g)^{-1}𝒪_S`-modules. The companion map \
`Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}`, in abelian sheaves, is \
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`."]
def deRhamPullbackChain :
    ((_root_.pullback (relativeBase f g)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Scheme.Hom.deRhamComplex g) ⟶
      Scheme.Hom.deRhamComplex (f ≫ g) :=
  (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _).symm (deRhamPushforwardChain f g)

end Stacks.DeRhamPullback

end

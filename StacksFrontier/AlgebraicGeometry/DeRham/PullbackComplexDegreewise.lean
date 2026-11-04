module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBaseProjection
import StacksCore.Tactic.StacksAttribute

/-!
# The degree-`n` component of the de Rham pullback map

Let `f : X ⟶ Y` be a morphism of schemes and `g : Y ⟶ S` the structure morphism of the target.
`Stacks.DeRhamPullback.deRhamPullbackChain` is the canonical morphism of complexes
`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` of `(f∘g)^{-1}𝒪_S`-modules, defined as the adjoint transpose
of the canonical map `Ω^•_{Y/S} ⟶ (relativeBase f g)_*Ω^•_{X/S}` and therefore opaque: nothing
about its components is visible from the definition.

This file computes them. The degree-`n` component factors as

`f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S} ≅ ⋀^n(f^*Ω_{Y/S}) ⟶ ⋀^nΩ_{X/S} = Ω^n_{X/S}`,

the comparison `f^{-1} ⟶ f^*` of
`StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison` followed by the
`𝒪_X`-linear canonical map `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` on
relative differential forms, whose coefficients are restricted along `(f∘g)^{-1}𝒪_S ⟶ 𝒪_X`.
The second factor is by construction the comparison of Tag 01CI for the exterior algebra
followed by the degree-`n` component of the graded-algebra homomorphism of Tag 0FLV, so the
factorization is exactly the one through `⋀^n(f^*Ω_{Y/S})` above.

## Main results

* `AlgebraicGeometry.Scheme.Hom.homEquiv_relativeDifferentialFormsMap`: the canonical map
  `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative differential forms is the adjoint transpose of the
  degree-`n` component of the graded-algebra homomorphism of Tag 07HX.
* `Stacks.DeRhamPullback.deRhamPullbackChain_f`: **the degreewise factorization of `ρ`.**
* `Stacks.DeRhamPullback.deRhamPullbackChain_f_exteriorPowerPullback`: the same, with the second
  factor written out as the comparison of Tag 01CI followed by the comparison of exterior
  algebras of Tag 0FLV.

## Implementation notes

Both factorizations of `ρ_n` are adjoint transposes, so the proof transposes the asserted
identity back along `f^{-1} ⊣ f_*` for the morphism of ringed spaces `relativeBase f g` and
compares the two resulting maps of `g^{-1}𝒪_S`-modules. On that side the comparison
`f^{-1} ⟶ f^*` is `Stacks.DeRhamDirectImage.relativeToPullbackLeg`, the unit of `f^* ⊣ f_*` read
through the square of ringed spaces, and `deRhamPushforwardChain` is the graded-algebra
homomorphism of Tag 07HX read through the same square; the two square transports agree because
both are the `eqToHom` of the commuting square, so after naturality the identity reduces to
`homEquiv_relativeDifferentialFormsMap`.

No step is a rewrite. The types here mix `Modules (inverseImageBase g)` with the
`SheafOfModules (underlyingRingSheaf ((TopCat.Sheaf.pullback _ g.base).obj S.sheaf))` spelling
of the de Rham complex; the two agree by `rfl` but not at reducible transparency, so every goal
that mentions both is rejected by the motive check of `rw` and `simp`, and the proofs are
composed from `Eq.trans` and `congrArg` instead.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace CategoryTheory.Adjunction

/-- **The adjoint transpose of a morphism of complexes is its degreewise transpose**, for the
adjunction induced degreewise by an adjunction of additive functors. -/
theorem mapHomologicalComplex_homEquiv_symm_f {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
    {ι : Type*} (c : ComplexShape ι) {K : HomologicalComplex A c} {L : HomologicalComplex B c}
    (ψ : K ⟶ (G.mapHomologicalComplex c).obj L) (n : ι) :
    (((adj.mapHomologicalComplex c).homEquiv K L).symm ψ).f n =
      (adj.homEquiv (K.X n) (L.X n)).symm (ψ.f n) := rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Hom

open SheafOfModules.GradedAlgebra

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)

/-- **Stacks Project, Tag 07HX.** The canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative
differential forms is the adjoint transpose of the degree-`n` component of the canonical
homomorphism of sheaves of graded algebras `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})`. -/
@[stacks 07HX "the linearized canonical map on forms is the transpose of the graded homomorphism"]
theorem homEquiv_relativeDifferentialFormsMap (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv
        (relativeDifferentialForms p n) (relativeDifferentialForms p' n)
        (relativeDifferentialFormsMap f p p' g hcomm n) =
      (deRhamFormsPushforwardHom f p p' g hcomm).app n :=
  (congrArg
    ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv
      (relativeDifferentialForms p n) (relativeDifferentialForms p' n))
    (relativeDifferentialFormsMap_eq_pullbackComparison f p p' g hcomm n)).trans
      (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRhamPullback

open Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The inverse of the `eqToIso` of an equality of morphisms of ringed spaces is, at a sheaf of
modules, the `eqToHom` of the corresponding equality of pushforwards. -/
theorem eqToIso_pushforward_inv_app {A B : RingedSpace.{u}} {m m' : A ⟶ B} (h : m = m')
    (M : Modules A) :
    (eqToIso (congrArg _root_.pushforward h)).inv.app M =
      eqToHom (congrArg (fun k : A ⟶ B => (_root_.pushforward k).obj M) h.symm) := by
  subst h
  rfl

/-- The identification of the two composite pushforwards of the square, written out: the two
coherence isomorphisms of Tag 0097 and the transport along the square. -/
theorem pushforwardSquareIso_inv_app_eq (M : Modules X.toRingedSpace) :
    (pushforwardSquareIso f g).inv.app M =
      (_root_.pushforwardComp f.toLRSHom.toShHom (toInverseImageBase g)).inv.app M ≫
        relativeSquareTransport f g M ≫
        (_root_.pushforwardComp (toInverseImageBase (f ≫ g))
          (relativeInverseImageProjection f g)).hom.app M := by
  rw [pushforwardSquareIso]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  exact congrArg (fun t => (_root_.pushforwardComp f.toLRSHom.toShHom
      (toInverseImageBase g)).inv.app M ≫ t ≫
      (_root_.pushforwardComp (toInverseImageBase (f ≫ g))
        (relativeInverseImageProjection f g)).hom.app M)
    (eqToIso_pushforward_inv_app (toInverseImageBase_relativeBase f g) M)

/-- **The transpose of the comparison `f^{-1}𝓕 ⟶ f^*𝓕` is the unit of `f^* ⊣ f_*` followed by
the identification of the two composite pushforwards of the square.** -/
theorem relativeToPullbackLeg_eq_pushforwardSquareIso (M : Modules Y.toRingedSpace) :
    relativeToPullbackLeg f g M =
      (_root_.pushforward (toInverseImageBase g)).map
          ((_root_.pullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M) ≫
        (pushforwardSquareIso f g).inv.app
          ((_root_.pullback f.toLRSHom.toShHom).obj M) :=
  (congrArg (fun t => (_root_.pushforward (toInverseImageBase g)).map
      ((_root_.pullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M) ≫ t)
    (pushforwardSquareIso_inv_app_eq f g
      ((_root_.pullback f.toLRSHom.toShHom).obj M))).symm

/-- Naturality of the identification of the two composite pushforwards of the square. -/
theorem pushforwardSquareIso_inv_naturality {M N : Modules X.toRingedSpace} (ψ : M ⟶ N) :
    (pushforwardSquareIso f g).inv.app M ≫
        (_root_.pushforward (relativeBase f g)).map
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).map ψ) =
      (_root_.pushforward (toInverseImageBase g)).map
          ((_root_.pushforward f.toLRSHom.toShHom).map ψ) ≫
        (pushforwardSquareIso f g).inv.app N :=
  ((pushforwardSquareIso f g).inv.naturality ψ).symm

/-- The degree-`n` component of the canonical homomorphism of Tag 07HX, read through the square,
is the transpose of the comparison `f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S}` followed by the canonical
map on relative differential forms. -/
theorem homEquiv_comp_relativeDifferentialFormsMap (n : ℕ) :
    (_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv
        ((_root_.pushforward (toInverseImageBase g)).obj
          (Scheme.Hom.relativeDifferentialForms g (n : ℤ)))
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)))
      (relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≫
        (_root_.pushforward (toInverseImageBase (f ≫ g))).map
          (Scheme.Hom.relativeDifferentialFormsMap f g (f ≫ g) (𝟙 S)
            ((Category.comp_id (f ≫ g)).symm) (n : ℤ))) =
      (_root_.pushforward (toInverseImageBase g)).map (formsPushforwardComponent f g n) ≫
        (pushforwardSquareIso f g).inv.app
          (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)) := by
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) ?_
  refine Eq.trans (congrArg (· ≫ _) ((homEquiv_relativeInverseImageToPullback f g _).trans
    (relativeToPullbackLeg_eq_pushforwardSquareIso f g _))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) (pushforwardSquareIso_inv_naturality f g _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (· ≫ _) ?_
  refine Eq.trans (Functor.map_comp _ _ _).symm ?_
  exact congrArg _
    (Scheme.Hom.homEquiv_relativeDifferentialFormsMap f g (f ≫ g) (𝟙 S)
      ((Category.comp_id (f ≫ g)).symm) (n : ℤ))

/-- The degree-`n` component of `ρ` is the transpose of the degree-`n` component of
`deRhamPushforwardChain`. -/
theorem deRhamPullbackChain_f_eq_homEquiv_symm (n : ℕ) :
    (deRhamPullbackChain f g).f n =
      ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv
          ((_root_.pushforward (toInverseImageBase g)).obj
            (Scheme.Hom.relativeDifferentialForms g (n : ℤ)))
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
            (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)))).symm
        (formsPushforward f g n) :=
  Adjunction.mapHomologicalComplex_homEquiv_symm_f _ _ _ n

/-- **The degreewise factorization of the de Rham pullback map.** The degree-`n` component of
`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` is the comparison `f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S}` followed
by the `𝒪_X`-linear canonical map `f^*Ω^n_{Y/S} ⟶ Ω^n_{X/S}` on relative differential forms,
with coefficients restricted along `(f∘g)^{-1}𝒪_S ⟶ 𝒪_X`. -/
@[stacks 07HX "the degree-n component of the canonical map f⁻¹Ω^•_{Y/S} ⟶ Ω^•_{X/S}"]
theorem deRhamPullbackChain_f (n : ℕ) :
    (deRhamPullbackChain f g).f n =
      relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≫
        (_root_.pushforward (toInverseImageBase (f ≫ g))).map
          (Scheme.Hom.relativeDifferentialFormsMap f g (f ≫ g) (𝟙 S)
            ((Category.comp_id (f ≫ g)).symm) (n : ℤ)) :=
  (deRhamPullbackChain_f_eq_homEquiv_symm f g n).trans
    ((congrArg (fun t => ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv
            ((_root_.pushforward (toInverseImageBase g)).obj
              (Scheme.Hom.relativeDifferentialForms g (n : ℤ)))
            ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
              (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)))).symm t)
        (homEquiv_comp_relativeDifferentialFormsMap f g n).symm).trans
      (Equiv.symm_apply_apply _ _))

/-- **The degreewise factorization of `ρ` through `⋀^n(f^*Ω_{Y/S})`**: the comparison
`f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S}`, the comparison `f^*(⋀^nΩ_{Y/S}) ≅ ⋀^n(f^*Ω_{Y/S})` of Tag
01CI, and the degree-`n` component of the homomorphism of exterior algebras of Tag 0FLV. -/
@[stacks 0FLV "the degree-n component of f⁻¹Ω^•_{Y/S} ⟶ Ω^•_{X/S} factors through ⋀ⁿ(f^*Ω_{Y/S})"]
theorem deRhamPullbackChain_f_exteriorPowerPullback (n : ℕ) :
    (deRhamPullbackChain f g).f n =
      relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≫
        (_root_.pushforward (toInverseImageBase (f ≫ g))).map
          (((Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
                (Scheme.Hom.relativeDifferentialFormsAlgebra g)
                (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g))
                (Scheme.Modules.exteriorAlgebra
                  ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g)))
                (Scheme.Modules.exteriorGenerator
                  ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g)))
                (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
                  (Scheme.Hom.relativeDifferentials g))
                (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)).app (n : ℤ)).hom ≫
            (Scheme.Hom.relativeDifferentialFormsComparison f g (f ≫ g) (𝟙 S)
              ((Category.comp_id (f ≫ g)).symm)).app (n : ℤ)) :=
  deRhamPullbackChain_f f g n

/-- **The de Rham pullback map on the pullback-unit sections.** On the image of a local section
of `Ω^n_{Y/S}` under the unit of `f^{-1} ⊣ f_*`, the degree-`n` component of `ρ` is the
degree-`n` component of the graded-algebra homomorphism of Tag 07HX. -/
theorem deRhamPullbackChain_f_val_app_unit (n : ℕ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : ((Scheme.Hom.deRhamComplex g).X n).val.obj U) :
    ((deRhamPullbackChain f g).f n).val.app ((opensMap (relativeBase f g)).op.obj U)
        (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
          ((Scheme.Hom.deRhamComplex g).X n)).val.app U x) =
      (formsPushforwardComponent f g n).val.app U x :=
  (congrArg (fun t => t.val.app ((opensMap (relativeBase f g)).op.obj U)
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X n)).val.app U x))
    (deRhamPullbackChain_f_eq_homEquiv_symm f g n)).trans
    ((SheafOfModules.GradedAlgebra.homEquiv_symm_val_app_unit (relativeBase f g)
        (formsPushforward f g n) U x).trans
      (pushforwardSquareIso_inv_val_app f g
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)) U
        ((formsPushforwardComponent f g n).val.app U x)))

/-- **The de Rham pullback map is multiplicative on the pullback-unit sections**: it carries the
wedge product of two pulled-back forms to the wedge product of their images. -/
theorem deRhamPullbackChain_f_val_app_unit_mul (i j : ℕ) (U : (Opens Y.carrier)ᵒᵖ)
    (a : ((Scheme.Hom.deRhamComplex g).X i).val.obj U)
    (b : ((Scheme.Hom.deRhamComplex g).X j).val.obj U) :
    ((deRhamPullbackChain f g).f (i + j)).val.app ((opensMap (relativeBase f g)).op.obj U)
        (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X (i + j))).val.app U
          (((Scheme.Hom.relativeDifferentialFormsAlgebra g).mul (i : ℤ) (j : ℤ)).app U a b)) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra (f ≫ g)).mul (i : ℤ) (j : ℤ)).app
          ((opensMap f.toLRSHom.toShHom).op.obj U)
        (((deRhamPullbackChain f g).f i).val.app ((opensMap (relativeBase f g)).op.obj U)
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X i)).val.app U a))
        (((deRhamPullbackChain f g).f j).val.app ((opensMap (relativeBase f g)).op.obj U)
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X j)).val.app U b)) :=
  (deRhamPullbackChain_f_val_app_unit f g (i + j) U _).trans
    (((Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S)
          ((Category.comp_id (f ≫ g)).symm)).map_mul (i : ℤ) (j : ℤ) U a b).trans
      (congrArg₂ (fun p q => ((Scheme.Hom.relativeDifferentialFormsAlgebra (f ≫ g)).mul
            (i : ℤ) (j : ℤ)).app ((opensMap f.toLRSHom.toShHom).op.obj U) p q)
        (deRhamPullbackChain_f_val_app_unit f g i U a).symm
        (deRhamPullbackChain_f_val_app_unit f g j U b).symm))

end Stacks.DeRhamPullback

end

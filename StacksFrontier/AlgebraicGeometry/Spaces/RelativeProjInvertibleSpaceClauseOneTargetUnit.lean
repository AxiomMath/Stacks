module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardUnitLaws
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIdUnitLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackIdIsoTransport

/-!
# The unit law of Stacks 03LU at a morphism equal to the identity, at a module

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` meets the
comparison `c^*q^* ≅ (c ≫ q)^*` of Stacks 03LU along a section `c` of `q` (`c ≫ q = 𝟙`), followed
by the transport along `c ≫ q = 𝟙` and the unit law `(𝟙)^* ≅ 𝟭`.  This file proves the unit law
of 03LU at a morphism `m = 𝟙`, between isomorphisms of functors and at a module, with the
comparisons typed through `AlgebraicGeometry.Space.modulePullbackCompHom` and
`AlgebraicGeometry.Space.modulePullbackCompInv` and the unit law through
`AlgebraicGeometry.Space.modulePullbackIdApp`, whose targets are spelled as iterated inverse
images and as the module itself.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_trans_eqToIso_of_eq_id`: the unit law at
  `m = 𝟙`, between isomorphisms of functors.
* `AlgebraicGeometry.Space.modulePullbackCompHom_comp_pullbackTransport_of_eq_id`,
  `AlgebraicGeometry.Space.modulePullbackCompInv_comp_pullbackTransport_comp_idApp`: the unit law
  at `m = 𝟙` at a module.

## Implementation notes

The components `(modulePullbackCompIso B S hS f g).hom.app M` have source
`(g^* ⋙ f^*).obj M`, and `(modulePullbackIdIso B S hS X).hom.app M` has target `(𝟭 _).obj M`.
A composite in which such a component meets a morphism spelled with `f^*(g^*M)` or `M` is
accepted by the elaborator, but the kernel compares the two spellings by unfolding
`AlgebraicGeometry.Space.modulePullback`, which is a deterministic timeout even at 800000
heartbeats (for instance for the inverse comparison followed by the unit law, rewritten in a composite).
With the comparisons and the unit law read through the definitions below, every statement is
spelled with iterated inverse images only, and the same rewriting is checked at once.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The component of the transport of the inverse image functors along an equality of morphisms
is the transport of the inverse images. -/
theorem eqToIso_hom_app_modulePullback {T Y : AlgebraicSpaces B S hS} {a b : T ⟶ Y} (h : a = b)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (eqToIso (congrArg (modulePullback B S hS) h)).hom.app N = pullbackTransport N h := by
  subst h
  rfl

/-- **The unit law of Stacks 03LU at a morphism equal to the identity, between isomorphisms of
functors**: for `m = 𝟙`, the comparison `m^*p^* ≅ (m ≫ p)^*` followed by the transport along
`m ≫ p = p` is the transport along `m = 𝟙` followed by the unit law `(𝟙)^* ≅ 𝟭`, whiskered with
`p^*`.  Stated between isomorphisms of functors, so that the substitution of `m` is not performed
at a component. -/
theorem modulePullbackCompIso_trans_eqToIso_of_eq_id {T Y : AlgebraicSpaces B S hS}
    {m : T ⟶ T} (hm : m = 𝟙 T) (p : T ⟶ Y) (hmp : m ≫ p = p) :
    modulePullbackCompIso B S hS m p ≪≫ eqToIso (congrArg (modulePullback B S hS) hmp) =
      Functor.isoWhiskerLeft (modulePullback B S hS p)
          (eqToIso (congrArg (modulePullback B S hS) hm) ≪≫ modulePullbackIdIso B S hS T) ≪≫
        (modulePullback B S hS p).rightUnitor := by
  subst hm
  refine (Stacks.CategoryTheory.trans_eqToIso_of_refl _ _).trans ?_
  refine ((modulePushforwardCoherence B S hS).modulePullbackCompIso_id_left p).trans ?_
  rw [modulePushforwardCoherence_modulePullbackIdIso]
  exact congrArg (fun e : modulePullback B S hS (𝟙 T) ≅ 𝟭 (Modules.{u, u} B S hS T.1 T.2) ↦
      Functor.isoWhiskerLeft (modulePullback B S hS p) e ≪≫ (modulePullback B S hS p).rightUnitor)
    (Stacks.CategoryTheory.eqToIso_of_refl_trans _ (modulePullbackIdIso B S hS T)).symm

/-- **The unit law of Stacks 03LU at a morphism equal to the identity**, at a module: for `m = 𝟙`,
the comparison `m^*p^*A ≅ (m ≫ p)^*A` followed by the transport along `m ≫ p = p` is the
transport along `m = 𝟙` followed by the unit law `(𝟙)^* ≅ 𝟭`. -/
theorem modulePullbackCompIso_hom_app_comp_pullbackTransport_of_eq_id
    {T Y : AlgebraicSpaces B S hS} {m : T ⟶ T} (hm : m = 𝟙 T) (p : T ⟶ Y) (hmp : m ≫ p = p)
    (A : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS m p).hom.app A ≫ pullbackTransport A hmp =
      pullbackTransport ((modulePullback B S hS p).obj A) hm ≫
        (modulePullbackIdIso B S hS T).hom.app ((modulePullback B S hS p).obj A) :=
  calc (modulePullbackCompIso B S hS m p).hom.app A ≫ pullbackTransport A hmp
      = (modulePullbackCompIso B S hS m p).hom.app A ≫
          (eqToIso (congrArg (modulePullback B S hS) hmp)).hom.app A := by
        rw [eqToIso_hom_app_modulePullback]
    _ = (modulePullbackCompIso B S hS m p ≪≫
          eqToIso (congrArg (modulePullback B S hS) hmp)).hom.app A :=
        (Stacks.CategoryTheory.trans_hom_app _ _ A).symm
    _ = (Functor.isoWhiskerLeft (modulePullback B S hS p)
          (eqToIso (congrArg (modulePullback B S hS) hm) ≪≫ modulePullbackIdIso B S hS T) ≪≫
          (modulePullback B S hS p).rightUnitor).hom.app A :=
        congrArg (fun e => e.hom.app A) (modulePullbackCompIso_trans_eqToIso_of_eq_id hm p hmp)
    _ = (eqToIso (congrArg (modulePullback B S hS) hm) ≪≫
          modulePullbackIdIso B S hS T).hom.app ((modulePullback B S hS p).obj A) :=
        Stacks.CategoryTheory.isoWhiskerLeft_trans_rightUnitor_hom_app _ _ A
    _ = (eqToIso (congrArg (modulePullback B S hS) hm)).hom.app
          ((modulePullback B S hS p).obj A) ≫
          (modulePullbackIdIso B S hS T).hom.app ((modulePullback B S hS p).obj A) :=
        Stacks.CategoryTheory.trans_hom_app _ _ _
    _ = pullbackTransport ((modulePullback B S hS p).obj A) hm ≫
          (modulePullbackIdIso B S hS T).hom.app ((modulePullback B S hS p).obj A) := by
        rw [eqToIso_hom_app_modulePullback]

/-- The unit law `(𝟙)^*M ≅ M` of Stacks 03LU at a module, with its target spelled `M` (rather than
`(𝟭 _).obj M`), so that composites with it never compare the two spellings. -/
def modulePullbackIdApp {T : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS T.1 T.2) :
    (modulePullback B S hS (𝟙 T)).obj M ⟶ M :=
  (modulePullbackIdIso B S hS T).hom.app M

/-- The unit law `(𝟙)^*M ≅ M` of Stacks 03LU is natural in `M`. -/
theorem modulePullbackIdApp_naturality {T : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS T.1 T.2} (φ : M ⟶ N) :
    (modulePullback B S hS (𝟙 T)).map φ ≫ modulePullbackIdApp N =
      modulePullbackIdApp M ≫ φ :=
  (modulePullbackIdIso B S hS T).hom.naturality φ

/-- **The unit law of Stacks 03LU at a morphism equal to the identity**, at a module, with the
comparison `AlgebraicGeometry.Space.modulePullbackCompHom` and the unit law
`AlgebraicGeometry.Space.modulePullbackIdApp`: for `m = 𝟙`, `m^*p^*A ⟶ (m ≫ p)^*A = p^*A` is the
transport along `m = 𝟙` followed by `(𝟙)^*(p^*A) ≅ p^*A`. -/
theorem modulePullbackCompHom_comp_pullbackTransport_of_eq_id {T Y : AlgebraicSpaces B S hS}
    {m : T ⟶ T} (hm : m = 𝟙 T) (p : T ⟶ Y) (hmp : m ≫ p = p)
    (A : Modules.{u, u} B S hS Y.1 Y.2) :
    modulePullbackCompHom B S hS m p A ≫ pullbackTransport A hmp =
      pullbackTransport ((modulePullback B S hS p).obj A) hm ≫
        modulePullbackIdApp ((modulePullback B S hS p).obj A) :=
  modulePullbackCompIso_hom_app_comp_pullbackTransport_of_eq_id hm p hmp A

/-- **The unit law of Stacks 03LU at a morphism equal to the identity, read from the inverse
comparison**: for `m = 𝟙`, `(m ≫ p)^*A ⟶ m^*p^*A`, followed by the transport along `m = 𝟙` and
`(𝟙)^*(p^*A) ≅ p^*A`, is the transport along `m ≫ p = p`. -/
theorem modulePullbackCompInv_comp_pullbackTransport_comp_idApp {T Y : AlgebraicSpaces B S hS}
    {m : T ⟶ T} (hm : m = 𝟙 T) (p : T ⟶ Y) (hmp : m ≫ p = p)
    (A : Modules.{u, u} B S hS Y.1 Y.2) :
    modulePullbackCompInv B S hS m p A ≫
        pullbackTransport ((modulePullback B S hS p).obj A) hm ≫
          modulePullbackIdApp ((modulePullback B S hS p).obj A) =
      pullbackTransport A hmp :=
  (congrArg (fun t => modulePullbackCompInv B S hS m p A ≫ t)
    (modulePullbackCompHom_comp_pullbackTransport_of_eq_id hm p hmp A)).symm.trans
      (modulePullbackCompInv_comp_compHom_assoc m p A _)

end AlgebraicGeometry.Space

end

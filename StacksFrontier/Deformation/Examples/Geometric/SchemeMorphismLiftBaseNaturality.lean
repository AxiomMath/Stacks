module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalBaseNaturality
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationCrossScalingConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismDerivationsHom
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftNamedTorsor
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermInteriorSourceCross

/-!
# The action of Tag 0CK2 on the lifts of a morphism is natural in the base object

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k`. For deformations `P` of `X`
and `Q` of `Y` and a global lift `ℓ₀ : P.scheme ⟶ Q.scheme` of `f`, the translation action of
[Stacks Project, Tag 0CK2] on the global lifts is named
`Deformation.Examples.globalLiftsOverBaseVAdd`. It is constructed at **one** base object of
`𝒞_Λ`. This file proves that it is natural in the base object.

Let `φ : P₁ ⟶ P₂` and `ψ : Q₁ ⟶ Q₂` be arrows of the two deformation categories over compatible
morphisms of bases. A global lift `ℓ` of `f` to `(P₁, Q₁)` pushes forward to a unique global lift
`π ℓ` to `(P₂, Q₂)` with `π ℓ ∘ ψ = φ ∘ ℓ` on total spaces
(`Deformation.Examples.globalLiftsOverBasePushforward`), because `Q₂` is the base change of `Q₁`.
The pushforward intertwines the two actions through an additive map of the acting groups,
`Deformation.Examples.liftActionTransport`:

`π (θ ⬝ ℓ) = τ θ ⬝ π ℓ`

for every lift `ℓ` (`Deformation.Examples.globalLiftsOverBasePushforward_vadd`). This is the
input any statement about the Schlessinger structure on `T Def_{X ⟶ Y}` consumes: a sum of two
tangent vectors is realized only over a doubled coordinate module, and the scalar action is
transport along `ε ↦ cε`, so comparing either with the action needs exactly this naturality along
the coordinate maps of `𝒞_Λ`. At the coordinate scaling of a first-order deformation the
transport is multiplication by the scalar
(`Deformation.Examples.liftActionTransport_crossScaling`).

## Main definitions

* `Deformation.Examples.globalLiftsOverBasePushforward`: the pushforward `π` of a global lift.
* `Deformation.Examples.liftActionTransport`: the transport `τ` of the acting group.

## Main results

* `Deformation.Examples.globalLiftsOverBaseVAdd_val`: the named action does not depend on its
  base point: on a lift `ℓ` it is the modified lift `θ ⬝ ℓ` of [Stacks Project, Tag 0CK1].
* `Deformation.Examples.globalLiftsOverBasePushforward_vadd`: **naturality of the action of
  [Stacks Project, Tag 0CK2] in the base object.**
* `Deformation.Examples.liftActionTransport_eq`, `Deformation.Examples.liftActionTransport_comp`
  and `Deformation.Examples.liftActionTransport_id`: the transport does not depend on the lift it
  is read at, and it is functorial.
* `Deformation.Examples.liftActionTransport_crossScaling`: along the coordinate scaling
  `ε ↦ cε` of the chosen first-order pushforward, the transport is multiplication by `c`.

## Implementation notes

The transport is defined at a base lift `ℓ₁`, as the unique element `τ θ` with
`π (θ ⬝ ℓ₁) = τ θ ⬝ π ℓ₁`, and only then shown to work at every lift. The content is the
thickening-level statement `Stacks.Thickenings.derivationActionGlobal_comp_of_comp`: compatibility
of the two actions with the vertical maps at one pair of lifts is a property of the two acting
data alone (`Stacks.Thickenings.DerivationSectionsCorrespond`), so it holds at every pair.

## References

* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The named action does not depend on its base point -/

section Val

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)

/-- **The named action of [Stacks Project, Tag 0CK2] on a lift is the modified lift of
[Stacks Project, Tag 0CK1].** Whatever the base point `ℓ₀`, translating `ℓ` by `θ` is `θ ⬝ ℓ`;
in particular the action does not depend on `ℓ₀`. -/
theorem globalLiftsOverBaseVAdd_val (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap)
    (ℓ : globalLiftsOverBase f P Q e) :
    (globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ).1 =
      Stacks.Thickenings.derivationActionGlobal (ker_specialMap_pow_two_eq_bot P hm)
        ((Stacks.Thickenings.pullbackCotangentSheafIsoOfBase Q.specialCartesian f).hom ≫ θ)
        ℓ.2.2 := by
  obtain ⟨κ, rfl⟩ := (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).surjective ℓ
  rw [globalLiftsOverBaseVAdd, Equiv.symm_apply_apply, globalLiftsOverBaseDerivationEquiv_val,
    Preadditive.comp_add,
    ← Stacks.Thickenings.derivationActionGlobal_derivationActionGlobal _ _ _ ℓ₀.2.2]
  exact Stacks.Thickenings.derivationActionGlobal_congr_base _ _ _ _
    (globalLiftsOverBaseDerivationEquiv_val f pX pY hf hm ℓ₀ κ).symm

/-- The named action does not depend on its base point. -/
theorem globalLiftsOverBaseVAdd_eq_vadd (ℓ₀ ℓ₀' : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap)
    (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ = globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀' θ ℓ :=
  Subtype.ext ((globalLiftsOverBaseVAdd_val f pX pY hf hm ℓ₀ θ ℓ).trans
    (globalLiftsOverBaseVAdd_val f pX pY hf hm ℓ₀' θ ℓ).symm)

end Val

/-! ### The pushforward of a global lift -/

section Pushforward

variable {P₁ P₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q₁ Q₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e₁ : Q₁.base ⟶ P₁.base} {e₂ : Q₂.base ⟶ P₂.base}
  (φ : P₁ ⟶ P₂) (ψ : Q₁ ⟶ Q₂) (hb : ψ.base ≫ e₂ = e₁ ≫ φ.base)

include hb in
/-- The square the pushforward of a lift is lifted through. -/
theorem globalLiftsOverBasePushforward_w (ℓ : globalLiftsOverBase f P₁ Q₁ e₁) :
    (φ.map ≫ ℓ.1) ≫ Q₁.toBase = deformationAmbientToBase P₂ e₂ ≫ baseSpecMap ψ.base := by
  rw [Category.assoc, ℓ.2.1, deformationAmbientToBase, deformationAmbientToBase,
    ← Category.assoc, φ.cartesian.w, Category.assoc, Category.assoc, ← baseSpecMap_comp,
    ← baseSpecMap_comp, hb]

include hf in
/-- **The pushforward of a global lift of `f` along a pair of arrows of deformations.** `Q₂` is
the base change of `Q₁`, so the composite `φ ∘ ℓ : P₂.scheme ⟶ Q₁.scheme` together with the
structure morphism of `P₂` factors uniquely through `Q₂.scheme`. -/
def globalLiftsOverBasePushforward (ℓ : globalLiftsOverBase f P₁ Q₁ e₁) :
    globalLiftsOverBase f P₂ Q₂ e₂ :=
  ⟨ψ.cartesian.lift (φ.map ≫ ℓ.1) (deformationAmbientToBase P₂ e₂)
      (globalLiftsOverBasePushforward_w f pX pY φ ψ hb ℓ),
    ψ.cartesian.lift_snd _ _ _, by
      refine ψ.cartesian.hom_ext ?_ ?_
      · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, φ.special_compat, ℓ.2.2,
          Category.assoc, ψ.special_compat]
      · rw [Category.assoc, IsPullback.lift_snd, Category.assoc, Q₂.specialCartesian.w,
          specialMap_comp_deformationAmbientToBase (X := Over.mk pX) (Y := Over.mk pY) f hf P₂ e₂,
          Category.assoc]⟩

/-- **The defining square of the pushforward.** -/
theorem globalLiftsOverBasePushforward_fac (ℓ : globalLiftsOverBase f P₁ Q₁ e₁) :
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ).1 ≫ ψ.map = φ.map ≫ ℓ.1 :=
  ψ.cartesian.lift_fst _ _ _

/-- **The pushforward is the only lift with its defining square.** -/
theorem eq_globalLiftsOverBasePushforward (ℓ : globalLiftsOverBase f P₁ Q₁ e₁)
    (ℓ₂ : globalLiftsOverBase f P₂ Q₂ e₂) (h : ℓ₂.1 ≫ ψ.map = φ.map ≫ ℓ.1) :
    ℓ₂ = globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ :=
  Subtype.ext (ψ.cartesian.hom_ext
    (h.trans (globalLiftsOverBasePushforward_fac f pX pY hf φ ψ hb ℓ).symm)
    (ℓ₂.2.1.trans (ψ.cartesian.lift_snd _ _ _).symm))

/-- The pushforward along the identity arrows is the identity. -/
theorem globalLiftsOverBasePushforward_id (hb' : (𝟙 Q₁ : Q₁ ⟶ Q₁).base ≫ e₁ =
      e₁ ≫ (𝟙 P₁ : P₁ ⟶ P₁).base) (ℓ : globalLiftsOverBase f P₁ Q₁ e₁) :
    globalLiftsOverBasePushforward f pX pY hf (𝟙 P₁) (𝟙 Q₁) hb' ℓ = ℓ :=
  (eq_globalLiftsOverBasePushforward f pX pY hf (𝟙 P₁) (𝟙 Q₁) hb' ℓ ℓ
    ((Category.comp_id ℓ.1).trans (Category.id_comp ℓ.1).symm)).symm

/-- The pushforward along a composite is the composite of the pushforwards. -/
theorem globalLiftsOverBasePushforward_comp {P₃ : SchemeDeformationCategory (Λ := Λ) (k := k)
      (Over.mk pX)} {Q₃ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e₃ : Q₃.base ⟶ P₃.base} (φ' : P₂ ⟶ P₃) (ψ' : Q₂ ⟶ Q₃) (hb' : ψ'.base ≫ e₃ = e₂ ≫ φ'.base)
    (hb'' : (ψ ≫ ψ').base ≫ e₃ = e₁ ≫ (φ ≫ φ').base) (ℓ : globalLiftsOverBase f P₁ Q₁ e₁) :
    globalLiftsOverBasePushforward f pX pY hf (φ ≫ φ') (ψ ≫ ψ') hb'' ℓ =
      globalLiftsOverBasePushforward f pX pY hf φ' ψ' hb'
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ) := by
  refine (eq_globalLiftsOverBasePushforward f pX pY hf (φ ≫ φ') (ψ ≫ ψ') hb'' ℓ _ ?_).symm
  change _ ≫ ψ'.map ≫ ψ.map = (φ'.map ≫ φ.map) ≫ ℓ.1
  rw [← Category.assoc, globalLiftsOverBasePushforward_fac, Category.assoc,
    globalLiftsOverBasePushforward_fac, Category.assoc]

end Pushforward

/-! ### Naturality of the action -/

section Transport

variable {P₁ P₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q₁ Q₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e₁ : Q₁.base ⟶ P₁.base} {e₂ : Q₂.base ⟶ P₂.base}
  (φ : P₁ ⟶ P₂) (ψ : Q₁ ⟶ Q₂) (hb : ψ.base ≫ e₂ = e₁ ≫ φ.base)
  (hm₁ : IsLocalRing.maximalIdeal P₁.base ^ 2 = ⊥)
  (hm₂ : IsLocalRing.maximalIdeal P₂.base ^ 2 = ⊥)

/-- **Compatibility of the two actions with the pushforward at one lift gives it at every
lift.** If the pushforward of the translate `θ₁ ⬝ ℓ` is the translate `θ₂ ⬝ π ℓ` for one lift
`ℓ`, then the same holds for every lift. This is
`Stacks.Thickenings.derivationActionGlobal_comp_of_comp` at the special-fibre immersions. -/
theorem globalLiftsOverBasePushforward_vadd_of_vadd
    (θ₁ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap)
    (θ₂ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₂.specialMap)
    {ℓ₀ ℓ : globalLiftsOverBase f P₁ Q₁ e₁} {κ₀ : globalLiftsOverBase f P₂ Q₂ e₂}
    (h : globalLiftsOverBasePushforward f pX pY hf φ ψ hb
        (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀ θ₁ ℓ) =
      globalLiftsOverBaseVAdd f pX pY hf hm₂ κ₀ θ₂
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ))
    (ℓ₀' ℓ' : globalLiftsOverBase f P₁ Q₁ e₁) (κ₀' : globalLiftsOverBase f P₂ Q₂ e₂) :
    globalLiftsOverBasePushforward f pX pY hf φ ψ hb
        (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀' θ₁ ℓ') =
      globalLiftsOverBaseVAdd f pX pY hf hm₂ κ₀' θ₂
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ') := by
  refine (eq_globalLiftsOverBasePushforward f pX pY hf φ ψ hb _ _ ?_).symm
  rw [globalLiftsOverBaseVAdd_val, globalLiftsOverBaseVAdd_val]
  have h' := congrArg Subtype.val h
  rw [globalLiftsOverBaseVAdd_val] at h'
  have hfac := globalLiftsOverBasePushforward_fac f pX pY hf φ ψ hb
    (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀ θ₁ ℓ)
  rw [h', globalLiftsOverBaseVAdd_val] at hfac
  exact Stacks.Thickenings.derivationActionGlobal_comp_of_comp
    (ker_specialMap_pow_two_eq_bot P₁ hm₁) (ker_specialMap_pow_two_eq_bot P₂ hm₂)
    φ.special_compat ψ.special_compat ℓ.2.2
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ).2.2
    (globalLiftsOverBasePushforward_fac f pX pY hf φ ψ hb ℓ) hfac ℓ'.2.2
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ').2.2
    (globalLiftsOverBasePushforward_fac f pX pY hf φ ψ hb ℓ')

/-- The transport of the acting group, read at a base lift `ℓ₁`: the element of the second
acting group carrying `π ℓ₁` to `π (θ ⬝ ℓ₁)`. -/
def liftActionTransportFun (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap) :
    Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₂.specialMap :=
  (globalLiftsOverBaseDerivationEquiv f pX pY hf hm₂
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)).symm
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb
      (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₁ θ ℓ₁))

/-- **Naturality of the action of [Stacks Project, Tag 0CK2] in the base object**, for the
transport read at a base lift. -/
theorem globalLiftsOverBasePushforward_vadd_fun (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap)
    (ℓ₀ ℓ : globalLiftsOverBase f P₁ Q₁ e₁) (κ₀ : globalLiftsOverBase f P₂ Q₂ e₂) :
    globalLiftsOverBasePushforward f pX pY hf φ ψ hb
        (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀ θ ℓ) =
      globalLiftsOverBaseVAdd f pX pY hf hm₂ κ₀
        (liftActionTransportFun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ)
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ) := by
  refine globalLiftsOverBasePushforward_vadd_of_vadd f pX pY hf φ ψ hb hm₁ hm₂ θ _
    (ℓ₀ := ℓ₁) (ℓ := ℓ₁) (κ₀ := globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁) ?_ ℓ₀ ℓ κ₀
  rw [globalLiftsOverBaseVAdd_base f pX pY hf hm₂
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁), liftActionTransportFun,
    Equiv.apply_symm_apply]

/-- **The transport of the acting group of [Stacks Project, Tag 0CK2] along a pair of arrows of
deformations**, read at a base lift `ℓ₁`; it does not depend on `ℓ₁`
(`Deformation.Examples.liftActionTransport_eq`). -/
def liftActionTransport (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁) :
    (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P₁.specialMap) →+
      (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P₂.specialMap) where
  toFun := liftActionTransportFun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁
  map_zero' := by
    rw [liftActionTransportFun, globalLiftsOverBaseVAdd_zero,
      globalLiftsOverBaseDerivationEquiv_symm_base]
  map_add' θ η := by
    have h := globalLiftsOverBasePushforward_vadd_fun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ ℓ₁
      (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₁ η ℓ₁)
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)
    rw [globalLiftsOverBasePushforward_vadd_fun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ η ℓ₁ ℓ₁
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁), ← globalLiftsOverBaseVAdd_add,
      ← globalLiftsOverBaseVAdd_add, globalLiftsOverBaseVAdd_base f pX pY hf hm₂
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)] at h
    change (globalLiftsOverBaseDerivationEquiv f pX pY hf hm₂
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)).symm _ = _
    rw [h, Equiv.symm_apply_apply]

/-- The transport, as an additive map, is the function `liftActionTransportFun` it is built
from. -/
theorem liftActionTransport_apply (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap) :
    liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ =
      liftActionTransportFun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ := rfl

/-- **Naturality of the action of [Stacks Project, Tag 0CK2] in the base object.** For arrows
`φ : P₁ ⟶ P₂` and `ψ : Q₁ ⟶ Q₂` over compatible morphisms of bases, pushing a translate forward
is translating the pushforward by the transported element:

`π (θ ⬝ ℓ) = τ θ ⬝ π ℓ`,

for every lift `ℓ` and every choice of base points of the two named actions. -/
theorem globalLiftsOverBasePushforward_vadd (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap)
    (ℓ₀ ℓ : globalLiftsOverBase f P₁ Q₁ e₁) (κ₀ : globalLiftsOverBase f P₂ Q₂ e₂) :
    globalLiftsOverBasePushforward f pX pY hf φ ψ hb
        (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀ θ ℓ) =
      globalLiftsOverBaseVAdd f pX pY hf hm₂ κ₀
        (liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ)
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ) :=
  globalLiftsOverBasePushforward_vadd_fun f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ ℓ₀ ℓ κ₀

/-- **The transport is pinned by naturality**: an element of the second acting group with the
property of `Deformation.Examples.globalLiftsOverBasePushforward_vadd` at one lift is the
transport. -/
theorem liftActionTransport_eq_of_vadd (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ₁ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap)
    (θ₂ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₂.specialMap)
    {ℓ₀ ℓ : globalLiftsOverBase f P₁ Q₁ e₁} {κ₀ : globalLiftsOverBase f P₂ Q₂ e₂}
    (h : globalLiftsOverBasePushforward f pX pY hf φ ψ hb
        (globalLiftsOverBaseVAdd f pX pY hf hm₁ ℓ₀ θ₁ ℓ) =
      globalLiftsOverBaseVAdd f pX pY hf hm₂ κ₀ θ₂
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ)) :
    liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ₁ = θ₂ := by
  have h₁ := globalLiftsOverBasePushforward_vadd_of_vadd f pX pY hf φ ψ hb hm₁ hm₂ θ₁ θ₂ h
    ℓ₁ ℓ₁ (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)
  rw [globalLiftsOverBaseVAdd_base f pX pY hf hm₂
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)] at h₁
  change (globalLiftsOverBaseDerivationEquiv f pX pY hf hm₂
    (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)).symm _ = _
  rw [h₁, Equiv.symm_apply_apply]

/-- **The transport does not depend on the lift it is read at.** -/
theorem liftActionTransport_eq (ℓ₁ ℓ₁' : globalLiftsOverBase f P₁ Q₁ e₁) :
    liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ =
      liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁' :=
  AddMonoidHom.ext fun θ => liftActionTransport_eq_of_vadd f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ _
    (globalLiftsOverBasePushforward_vadd f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁' θ ℓ₁' ℓ₁'
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁'))

/-- **The transport along the identity arrows is the identity.** -/
theorem liftActionTransport_id (hb' : (𝟙 Q₁ : Q₁ ⟶ Q₁).base ≫ e₁ =
      e₁ ≫ (𝟙 P₁ : P₁ ⟶ P₁).base) (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap) :
    liftActionTransport f pX pY hf (𝟙 P₁) (𝟙 Q₁) hb' hm₁ hm₁ ℓ₁ θ = θ :=
  liftActionTransport_eq_of_vadd f pX pY hf (𝟙 P₁) (𝟙 Q₁) hb' hm₁ hm₁ ℓ₁ θ θ
    (ℓ₀ := ℓ₁) (ℓ := ℓ₁) (κ₀ := ℓ₁) (by
      rw [globalLiftsOverBasePushforward_id, globalLiftsOverBasePushforward_id])

/-- **The transport along a composite is the composite of the transports.** -/
theorem liftActionTransport_comp {P₃ : SchemeDeformationCategory (Λ := Λ) (k := k)
      (Over.mk pX)} {Q₃ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e₃ : Q₃.base ⟶ P₃.base} (φ' : P₂ ⟶ P₃) (ψ' : Q₂ ⟶ Q₃) (hb' : ψ'.base ≫ e₃ = e₂ ≫ φ'.base)
    (hb'' : (ψ ≫ ψ').base ≫ e₃ = e₁ ≫ (φ ≫ φ').base)
    (hm₃ : IsLocalRing.maximalIdeal P₃.base ^ 2 = ⊥) (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P₁.specialMap) :
    liftActionTransport f pX pY hf (φ ≫ φ') (ψ ≫ ψ') hb'' hm₁ hm₃ ℓ₁ θ =
      liftActionTransport f pX pY hf φ' ψ' hb' hm₂ hm₃
        (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)
        (liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ) := by
  refine liftActionTransport_eq_of_vadd f pX pY hf (φ ≫ φ') (ψ ≫ ψ') hb'' hm₁ hm₃ ℓ₁ θ _
    (ℓ₀ := ℓ₁) (ℓ := ℓ₁)
    (κ₀ := globalLiftsOverBasePushforward f pX pY hf φ' ψ' hb'
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)) ?_
  rw [globalLiftsOverBasePushforward_comp f pX pY hf φ ψ hb φ' ψ' hb' hb'',
    globalLiftsOverBasePushforward_comp f pX pY hf φ ψ hb φ' ψ' hb' hb'',
    globalLiftsOverBasePushforward_vadd f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ θ ℓ₁ ℓ₁
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁),
    globalLiftsOverBasePushforward_vadd f pX pY hf φ' ψ' hb' hm₂ hm₃
      (globalLiftsOverBasePushforward f pX pY hf φ ψ hb ℓ₁)]

end Transport

/-! ### The transport along the coordinate scaling is multiplication by the scalar -/

section Scaling

include hf in
/-- **The scalar action of `k` on a sheaf of `𝒪_X`-modules, on sections**: for the `k`-linear
structure `AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))`, the endomorphism `c • 𝟙` acts on
sections over `U` as multiplication by the function `c` determines on `U`. -/
theorem smul_id_app_apply (c : k) (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
    (Scheme.Modules.Hom.app (c • 𝟙 M) U).hom s = baseSection pX c U • s := by
  subst hf
  rfl

variable {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
    y₀)

/-- **The coordinate scaling `ε ↦ cε` of the chosen re-based first-order pushforward**, as a
self-arrow of the deformation category: the arrow between chosen pushforwards induced by
`k[c • 𝟙]`. -/
abbrev crossScaling {Z : Over (Spec (CommRingCat.of k))}
    {z₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (Q : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) z₀)
    (c : k) : firstOrderPushforwardCross Q ⟶ firstOrderPushforwardCross Q :=
  Q.map (squareZeroCrossUnderMap.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj z₀)
    (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))))

private theorem eqToHom_conj_comm {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (hA : A = C)
    (hB : B = C) (g : C ⟶ C) :
    (eqToHom hA ≫ g ≫ eqToHom hA.symm) ≫ eqToHom (hA.trans hB.symm) =
      eqToHom (hA.trans hB.symm) ≫ eqToHom hB ≫ g ≫ eqToHom hB.symm := by
  subst hA hB
  simp

/-- The two coordinate scalings lie over compatible morphisms of bases. -/
theorem crossScaling_base_comp (c : k) :
    (crossScaling QY c).base ≫ eqToHom ((firstOrderPushforwardCross_base QY).trans
        (firstOrderPushforwardCross_base QX).symm) =
      eqToHom ((firstOrderPushforwardCross_base QY).trans
        (firstOrderPushforwardCross_base QX).symm) ≫ (crossScaling QX c).base := by
  rw [crossScaling, crossScaling, map_squareZeroCrossUnderMap_base,
    map_squareZeroCrossUnderMap_base]
  exact eqToHom_conj_comm _ _ _

/-- **The transport of the acting group of [Stacks Project, Tag 0CK2] along the coordinate
scaling `ε ↦ cε` is multiplication by `c`.** The scaling of the chosen re-based first-order
pushforward acts on the conormal sheaf of its special fibre as multiplication by `c`
(`Deformation.Examples.conormalSelfMap_crossScaling_eq_smul`), so the perturbation of `θ` is
carried to the perturbation of `c • θ`, and naturality in the thickening
(`Stacks.Thickenings.derivationActionGlobal_comp_of_correspond`) does the rest. The `k`-linear
structure is the one of `Deformation.Examples.schemeMorphismDerivationsLinearEquivHom`. -/
theorem liftActionTransport_crossScaling (c : k)
    (hm : IsLocalRing.maximalIdeal (firstOrderPushforwardCross QX).base ^ 2 = ⊥)
    (ℓ₁ : globalLiftsOverBase f (firstOrderPushforwardCross QX) (firstOrderPushforwardCross QY)
      (eqToHom ((firstOrderPushforwardCross_base QY).trans
        (firstOrderPushforwardCross_base QX).symm)))
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules (firstOrderPushforwardCross QX).specialMap) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
    liftActionTransport f pX pY hf (crossScaling QX c) (crossScaling QY c)
      (crossScaling_base_comp pX pY QX QY c) hm hm ℓ₁ θ = c • θ := by
  let : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
  have hsq := ker_specialMap_pow_two_eq_bot (firstOrderPushforwardCross QX) hm
  have hc : Stacks.Thickenings.IsConormalMapOver hsq hsq (crossScaling QX c).special_compat
      (c • 𝟙 (Stacks.Thickenings.conormalModules (firstOrderPushforwardCross QX).specialMap :
        X.Modules)) := by
    intro V s
    rw [← Stacks.Thickenings.conormalSection_conormalSelfMap hsq (crossScaling QX c).special_compat
        V s,
      conormalSelfMap_crossScaling_eq_smul hsq (firstOrderPushforwardCross_base QX) c
        (crossScaling QX c) (map_squareZeroCrossUnderMap_base QX _) V s,
      smul_id_app_apply f pX pY hf]
    rfl
  have hθ₂ : (Stacks.Thickenings.pullbackCotangentSheafIsoOfBase
        (firstOrderPushforwardCross QY).specialCartesian f).hom ≫ (c • θ) =
      ((Stacks.Thickenings.pullbackCotangentSheafIsoOfBase
        (firstOrderPushforwardCross QY).specialCartesian f).hom ≫ θ) ≫
        (c • 𝟙 (Stacks.Thickenings.conormalModules (firstOrderPushforwardCross QX).specialMap :
        X.Modules)) := by
    rw [Linear.comp_smul, Linear.comp_smul, Category.comp_id]
  refine liftActionTransport_eq_of_vadd f pX pY hf _ _ _ hm hm ℓ₁ θ (c • θ) (ℓ₀ := ℓ₁) (ℓ := ℓ₁)
    (κ₀ := globalLiftsOverBasePushforward f pX pY hf _ _
      (crossScaling_base_comp pX pY QX QY c) ℓ₁) ?_
  refine (eq_globalLiftsOverBasePushforward f pX pY hf _ _ _ _ _ ?_).symm
  rw [globalLiftsOverBaseVAdd_val, globalLiftsOverBaseVAdd_val]
  refine Stacks.Thickenings.derivationActionGlobal_comp_of_correspond hsq hsq
    (crossScaling QX c).special_compat (crossScaling QY c).special_compat ?_ ℓ₁.2.2 _
    (globalLiftsOverBasePushforward_fac f pX pY hf _ _ _ ℓ₁)
  refine Stacks.Thickenings.correspond_of_isConormalMapOver hsq hsq _ _ hc fun A U h y => ?_
  rw [hθ₂]
  rfl

end Scaling

end Deformation.Examples

end

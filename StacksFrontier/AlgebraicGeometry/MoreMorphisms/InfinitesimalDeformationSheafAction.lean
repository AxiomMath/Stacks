module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafDerivation

/-!
# The action of a derivation on a lift, at sheaf level

Let `i : T ⟶ T'` be a first-order thickening, let `j : Y ⟶ Y'` be a morphism, let `a : T ⟶ Y`
have a lift `a' : T' ⟶ Y'` along `j`, and let `θ : a^*Ω_{Y/S} ⟶ 𝒞_{T/T'}` be an `𝒪_T`-linear
map. [Stacks Project, Tag 02H5] moves `a'` to a second lift `θ ⬝ a'`, uniquely characterised by
the comorphism equation `(θ ⬝ a')^♯ = (a')^♯ + D ∘ j^♯` with `D = θ ∘ d_{Y/S}` the derivation of
Equation [Stacks Project, Tag 04BV].

This file **constructs** that lift for arbitrary schemes — no affineness anywhere — as the
perturbation of `a'` by the square-zero derivation `D` of
`Stacks.Thickenings.derivationSectionι`, and proves that it satisfies the characterising equation
`Stacks.Thickenings.IsDerivationAction`. Together with
`Stacks.Thickenings.eq_of_isDerivationAction` this is the existence-and-uniqueness statement at
sheaf level.

## Main definitions

* `Stacks.Thickenings.derivationPerturbation`: the derivation `D` packaged as a
  `Stacks.Thickenings.SquareZeroPerturbation` of `a'`.
* `Stacks.Thickenings.derivationActionSheaf`: the lift `θ ⬝ a'`.

## Main results

* `Stacks.Thickenings.derivationActionSheaf_app`: its comorphism is `(a')^♯ + D ∘ j^♯`.
* `Stacks.Thickenings.derivationActionSheaf_comm`: it is again a lift of `a` along `j`.
* `Stacks.Thickenings.derivationActionSheaf_comp`: it is again a morphism over the base `S`.
* `Stacks.Thickenings.isDerivationAction_derivationActionSheaf`: it satisfies the relation
  `Stacks.Thickenings.IsDerivationAction`, so it *is* `θ ⬝ a'`.
* `Stacks.Thickenings.existsUnique_isDerivationAction` and
  `Stacks.Thickenings.existsUnique_isDerivationAction_over`: exactly one morphism, respectively
  exactly one morphism over `S`, is `θ ⬝ a'`.
* `Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm`:
  **[Stacks Project, Tag 04BZ]** for arbitrary schemes with the two lifts *constructed* rather
  than assumed.

## Implementation notes

The construction is `Stacks.Thickenings.SquareZeroPerturbation.perturb` applied to the datum
whose value on a section `s` of `𝒪_{Y'}` over `V` is `D (j^♯ s)`. The four algebraic conditions
that datum has to satisfy are exactly the four properties of
`Stacks.Thickenings.derivationSectionι` proved in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafDerivation.lean`:
additivity, the Leibniz rule along `(a')^♯`, the vanishing of a product of two values — both lie
in the square-zero defining ideal of `i` — and naturality in `V`. The vanishing of `D` on `1` is
not proved there but read off the Leibniz rule at `s = t = 1`, which gives `D 1 = D 1 + D 1`.

Because the perturbed morphism has the *same underlying continuous map* as `a'`, every transport
along an equality of opens occurring in `Stacks.Thickenings.IsDerivationAction` is a restriction
map from an open to itself, hence the identity
(`Stacks.Thickenings.presheaf_map_self`). That is what makes the characterising equation hold
with no bookkeeping: it reduces to `Stacks.Thickenings.SquareZeroPerturbation.perturb_app`.

### No `@[stacks 02H5]` or `@[stacks 0CK1]`

Three of the four clauses of [Stacks Project, Tag 02H5] are proved here for arbitrary schemes:
that `θ ⬝ a'` restricts to the same `a` on the closed subschemes
(`Stacks.Thickenings.derivationActionSheaf_comm`), that it is again a morphism over the base
(`Stacks.Thickenings.derivationActionSheaf_comp`), and the equation relating it to `θ`, in the
comorphism form `Stacks.Thickenings.IsDerivationAction`, together with the uniqueness it
forces. The two remaining parts of the source are proved elsewhere, both in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDerivationActionDifference.lean` and both for
arbitrary schemes:

* condition (2) of [Stacks Project, Tag 04FG], that `θ ⬝ a'` induces the *same map of conormal
  sheaves* as `a'`, is
  `Stacks.Thickenings.immersionConormalSheafMap_derivationActionSheaf`. The route is
  `Stacks.Immersion.immersionConormalSheafMap_unique`, which asks for the affine
  characterisation `Stacks.Immersion.IsInducedConormalSheafMap`; no affine chart is chosen,
  since the charts are the ones that characterisation quantifies over.
* the equation of the source read through the *difference derivation* of the unrestricted
  [Stacks Project, Tag 04FG] — that derivation being
  `Stacks.Thickenings.differenceDerivation` of
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationSheaf.lean` — is
  `Stacks.Thickenings.differenceDerivation_derivationActionSheaf`, which carries the attribute
  for [Stacks Project, Tag 0CK1]. `Stacks.Thickenings.IsDerivationAction` is the same assertion
  written with the comorphisms themselves, which is why nothing here needs that derivation.

So no `@[stacks 02H5]` or `@[stacks 0CK1]` attribute is placed by this file; what the file does
place is `@[stacks 04BZ]`, whose statement needs neither of those two parts.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Opposite TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {S T T' Y Y' : Scheme.{u}} {i : T ⟶ T'} {j : Y ⟶ Y'} {a : T ⟶ Y} {a' : T' ⟶ Y'}
  [IsClosedImmersion i]

variable (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
  (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
    Stacks.Conormal.conormalSheaf i)

/-! ### The derivation as a square-zero perturbation of the lift -/

/-- **The derivation `D = θ ∘ d_{Y/S}` as a square-zero perturbation of the lift `a'`.** Its
value on a section `s` of `𝒪_{Y'}` over `V` is `D (j^♯ s)`, a section of the defining ideal of
`i` over `a'⁻¹V`.

The Leibniz rule is `Stacks.Thickenings.derivationSectionι_leibniz`, the vanishing of products
is `Stacks.Thickenings.derivationSectionι_mul_derivationSectionι` and naturality is
`Stacks.Thickenings.derivationSectionι_naturality`. -/
def derivationPerturbation : SquareZeroPerturbation a' where
  value V s := derivationSectionι hi q ca θ V ((j.app V).hom s)
  value_zero V := by
    have h : (j.app V).hom (0 : Γ(Y', V)) = 0 := map_zero _
    rw [h]
    exact derivationSectionι_zero hi q ca θ V
  value_one V := by
    have h := derivationSectionι_leibniz hi q ca θ V 1 1
    have h1 : (1 : Γ(Y', V)) * 1 = 1 := one_mul 1
    have h2 : (a'.app V).hom (1 : Γ(Y', V)) = 1 := map_one _
    rw [h1, h2, one_mul] at h
    have h3 : derivationSectionι hi q ca θ V ((j.app V).hom 1) + 0 =
        derivationSectionι hi q ca θ V ((j.app V).hom 1) +
          derivationSectionι hi q ca θ V ((j.app V).hom 1) := by
      rw [add_zero]; exact h
    exact (add_left_cancel h3).symm
  value_add V s t := by
    have h : (j.app V).hom (s + t) = (j.app V).hom s + (j.app V).hom t := map_add _ _ _
    rw [h]
    exact derivationSectionι_add hi q ca θ V _ _
  value_leibniz V s t := derivationSectionι_leibniz hi q ca θ V s t
  value_mul_value V s t :=
    derivationSectionι_mul_derivationSectionι hi q ca θ V ((j.app V).hom s) ((j.app V).hom t)
  value_naturality hWV s := by
    have hj : (j.app _).hom ((Y'.presheaf.map (homOfLE hWV).op).hom s) =
        (Y.presheaf.map (homOfLE (j.preimage_mono hWV)).op).hom ((j.app _).hom s) :=
      app_presheaf_map j (homOfLE hWV).op s
    exact (congrArg (derivationSectionι hi q ca θ _) hj).trans
      (derivationSectionι_naturality hi q ca θ hWV _)

/-- The value of `Stacks.Thickenings.derivationPerturbation` is
`Stacks.Thickenings.derivationSectionι` of the pulled-back section. -/
theorem derivationPerturbation_value (V : Y'.Opens) (s : Γ(Y', V)) :
    (derivationPerturbation hi q ca θ).value V s =
      derivationSectionι hi q ca θ V ((j.app V).hom s) :=
  rfl

/-! ### The lift `θ ⬝ a'` -/

/-- **The lift `θ ⬝ a'` of [Stacks Project, Tag 0CK1], for arbitrary schemes.** The morphism
`T' ⟶ Y'` with the same underlying map as `a'` and comorphism `(a')^♯ + D ∘ j^♯`, where
`D = θ ∘ d_{Y/S}` is the derivation of Equation [Stacks Project, Tag 04BV].

This is the existence half of [Stacks Project, Tag 02H5] at sheaf level: by
`Stacks.Thickenings.isDerivationAction_derivationActionSheaf` it satisfies the characterising
relation `Stacks.Thickenings.IsDerivationAction`, and by
`Stacks.Thickenings.eq_of_isDerivationAction` it is the only morphism that does. -/
def derivationActionSheaf : T' ⟶ Y' :=
  (derivationPerturbation hi q ca θ).perturb

/-- The underlying map of `θ ⬝ a'` is that of `a'`. -/
@[simp]
theorem derivationActionSheaf_base : (derivationActionSheaf hi q ca θ).base = a'.base := rfl

/-- `θ ⬝ a'` and `a'` have the same preimages of opens. -/
theorem derivationActionSheaf_preimage (V : Y'.Opens) :
    derivationActionSheaf hi q ca θ ⁻¹ᵁ V = a' ⁻¹ᵁ V := rfl

/-- **The comorphism of `θ ⬝ a'` is `(a')^♯ + D ∘ j^♯`.** -/
theorem derivationActionSheaf_app (V : Y'.Opens) (s : Γ(Y', V)) :
    ((derivationActionSheaf hi q ca θ).app V).hom s =
      @HAdd.hAdd Γ(T', a' ⁻¹ᵁ V) Γ(T', a' ⁻¹ᵁ V) Γ(T', a' ⁻¹ᵁ V) inferInstance
        ((a'.app V).hom s) (derivationSectionι hi q ca θ V ((j.app V).hom s)) :=
  SquareZeroPerturbation.perturb_app (derivationPerturbation hi q ca θ) V s

/-- A ring map killing the perturbation of `s` does not distinguish `θ ⬝ a'` from `a'` on `s`. -/
private theorem map_derivationActionSheaf_app_eq {R : Type*} [Semiring R] (V : Y'.Opens)
    (s : Γ(Y', V)) (φ : Γ(T', a' ⁻¹ᵁ V) →+* R)
    (h : φ (derivationSectionι hi q ca θ V ((j.app V).hom s)) = 0) :
    φ (((derivationActionSheaf hi q ca θ).app V).hom s) = φ ((a'.app V).hom s) := by
  rw [derivationActionSheaf_app, map_add, h, add_zero]

/-- **`θ ⬝ a'` is again a lift of `a` along `j`.** The perturbation takes values in the defining
ideal of `i`, so it disappears after composing with `i`. -/
theorem derivationActionSheaf_comm : i ≫ derivationActionSheaf hi q ca θ = a ≫ j := by
  refine Eq.trans ?_ ca
  refine Scheme.Hom.ext rfl (fun V ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_))
  refine (CommRingCat.comp_apply _ _ s).trans ((presheaf_map_self _ _).trans ?_)
  exact map_derivationActionSheaf_app_eq hi q ca θ V s (i.app (a' ⁻¹ᵁ V)).hom
    (app_derivationSectionι_eq_zero hi q ca θ V _)

/-- **`θ ⬝ a'` is again a morphism over the base `S`.** The perturbation kills the sections of
`𝒪_Y` that come from `𝒪_S`, because the universal relative derivation does
(`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_d_app_eq_zero`). -/
theorem derivationActionSheaf_comp {p : T' ⟶ S} (ha' : a' ≫ q = p) :
    derivationActionSheaf hi q ca θ ≫ q = p := by
  refine Eq.trans ?_ ha'
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
  refine (CommRingCat.comp_apply _ _ r).trans ((presheaf_map_self _ _).trans ?_)
  exact map_derivationActionSheaf_app_eq hi q ca θ (q ⁻¹ᵁ W) ((q.app W).hom r) (RingHom.id _)
    (derivationSectionι_app_comp_eq_zero hi q ca θ W r)

/-! ### The characterising relation -/

/-- **`θ ⬝ a'` satisfies the relation that characterises it**, the existence half of
[Stacks Project, Tag 02H5] at sheaf level: the comorphism of
`Stacks.Thickenings.derivationActionSheaf` is `(a')^♯` plus the derivation `D` precomposed with
`j^♯`.

Both lifts have the same underlying map, so the transport along the equality of opens in
`Stacks.Thickenings.IsDerivationAction` is the identity. -/
theorem isDerivationAction_derivationActionSheaf :
    IsDerivationAction hi q ca (derivationActionSheaf_comm hi q ca θ) θ := fun V s ↦
  (presheaf_map_self _ _).trans (derivationActionSheaf_app hi q ca θ V s).symm

/-- **Exactly one morphism is `θ ⬝ a'`**, [Stacks Project, Tag 02H5] at sheaf level in the
formulation of `Stacks.Thickenings.IsDerivationAction`. Existence is
`Stacks.Thickenings.derivationActionSheaf`, uniqueness is
`Stacks.Thickenings.eq_of_isDerivationAction`.

The clause of the source that the new lift is again a morphism over the base is not included;
see the implementation notes of this file. -/
theorem existsUnique_isDerivationAction :
    ∃! b' : T' ⟶ Y', ∃ cb : i ≫ b' = a ≫ j, IsDerivationAction hi q ca cb θ :=
  ⟨derivationActionSheaf hi q ca θ,
    ⟨derivationActionSheaf_comm hi q ca θ, isDerivationAction_derivationActionSheaf hi q ca θ⟩,
    fun _ ⟨cc, hc⟩ ↦
      eq_of_isDerivationAction hi q ca cc (derivationActionSheaf_comm hi q ca θ) hc
        (isDerivationAction_derivationActionSheaf hi q ca θ)⟩

/-- **Exactly one morphism over `S` is `θ ⬝ a'`**, the same statement as
`Stacks.Thickenings.existsUnique_isDerivationAction` with the clause of
[Stacks Project, Tag 02H5] that the new lift is again a morphism over the base included. -/
theorem existsUnique_isDerivationAction_over {p : T' ⟶ S} (ha' : a' ≫ q = p) :
    ∃! b' : T' ⟶ Y', ∃ (cb : i ≫ b' = a ≫ j) (_ : b' ≫ q = p),
      IsDerivationAction hi q ca cb θ :=
  ⟨derivationActionSheaf hi q ca θ,
    ⟨derivationActionSheaf_comm hi q ca θ, derivationActionSheaf_comp hi q ca θ ha',
      isDerivationAction_derivationActionSheaf hi q ca θ⟩,
    fun _ ⟨cc, _, hc⟩ ↦
      eq_of_isDerivationAction hi q ca cc (derivationActionSheaf_comm hi q ca θ) hc
        (isDerivationAction_derivationActionSheaf hi q ca θ)⟩

/-! ### The compatibility of the actions, with the actions constructed -/

section Comm

variable {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u}}
  {i₁ : T₁ ⟶ T₁'} {i₂ : T₂ ⟶ T₂'} {j₁ : X₁ ⟶ X₁'} {j₂ : X₂ ⟶ X₂'}
  {a₁ : T₁ ⟶ X₁} {a₁' : T₁' ⟶ X₁'} {a₂ : T₂ ⟶ X₂} {a₂' : T₂' ⟶ X₂'}
  {h : T₂ ⟶ T₁} {h' : T₂' ⟶ T₁'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂]

/-- **Acting by compatible derivation data commutes with the vertical maps**,
[Stacks Project, Tag 04BZ] for arbitrary schemes, with both actions *constructed*. Let `(h, h')`
and `(f, f')` be the vertical maps of a diagram of first-order thickenings as in
[Stacks Project, Tag 04BY], let `(a₁, a₁')` and `(a₂, a₂')` be morphisms of thickenings
compatible with them, and let `p₁ : X₁' ⟶ S₁` and `p₂ : X₂' ⟶ S₂` be the structure morphisms.
Nothing is assumed étale and nothing is assumed affine. Given
`θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` and `θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` whose derivations
`D_n = θ_n ∘ d_{X_n/S_n}` of Equation [Stacks Project, Tag 04BV] satisfy
`D₂ (f^♯ y) = (h')^♯ (D₁ y)` — the commuting square of the source, read inside the ambient
structure sheaves — the lifts `θ₁ ⬝ a₁'` and `θ₂ ⬝ a₂'` of [Stacks Project, Tag 0CK1] give a
commutative square:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```

This is `Stacks.Thickenings.derivationAction_comp_of_derivationSection_comm` with its two
hypotheses `Stacks.Thickenings.IsDerivationAction` discharged by
`Stacks.Thickenings.isDerivationAction_derivationActionSheaf`: the lifts are the morphisms
constructed by `Stacks.Thickenings.derivationActionSheaf`, not morphisms assumed to satisfy a
relation. -/
@[stacks 04BZ "the two actions of Tag 0CK1 constructed by Stacks.Thickenings.derivationActionSheaf"]
theorem derivationActionSheaf_comp_of_derivationSection_comm
    (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (p₁ : X₁' ⟶ S₁) (p₂ : X₂' ⟶ S₂)
    (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁) (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cj : j₂ ≫ f' = f ≫ j₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cA : a₂' ≫ f' = h' ≫ a₁')
    {θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁}
    {θ₂ : (Scheme.Modules.pullback a₂).obj (Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)) ⟶
      Stacks.Conormal.conormalSheaf i₂}
    (hθ : ∀ (V : X₁'.Opens) (s : Γ(X₁', V)),
      (T₂'.presheaf.map (eqToHom (preimage_comp_eq cA V)).op).hom
          ((h'.app (a₁' ⁻¹ᵁ V)).hom (derivationSectionι hi₁ p₁ ca₁ θ₁ V ((j₁.app V).hom s)))
        = derivationSectionι hi₂ p₂ ca₂ θ₂ (f' ⁻¹ᵁ V)
            ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s))) :
    derivationActionSheaf hi₂ p₂ ca₂ θ₂ ≫ f' = h' ≫ derivationActionSheaf hi₁ p₁ ca₁ θ₁ :=
  derivationAction_comp_of_derivationSection_comm hi₁ hi₂ p₁ p₂ ca₁
    (derivationActionSheaf_comm hi₁ p₁ ca₁ θ₁) ca₂
    (derivationActionSheaf_comm hi₂ p₂ ca₂ θ₂) cT cj cX cA
    (isDerivationAction_derivationActionSheaf hi₁ p₁ ca₁ θ₁)
    (isDerivationAction_derivationActionSheaf hi₂ p₂ ca₂ θ₂) hθ

end Comm

end Stacks.Thickenings

end

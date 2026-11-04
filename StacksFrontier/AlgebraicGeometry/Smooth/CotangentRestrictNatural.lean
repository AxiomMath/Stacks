module

public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothGlobal

/-!
# The sections of `a^*Ω_{X/S}` over an affine open, naturally in the open

Let `f : X ⟶ S` and `a : T ⟶ X` be morphisms of schemes and let `U` be an open of `T`. The
isomorphism `Stacks.Smooth.restrictPullbackCotangentSheafIso` identifies the restriction of
`a^*Ω_{X/S}` to `U` with the pullback `(U.ι ≫ a)^*Ω_{X/S}` of `Ω_{X/S}` along the restricted
morphism, but only as an isomorphism of sheaves of modules: nothing says how it acts on the
pullback `Stacks.Smooth.pullbackD` of the universal differential, and without that it cannot
transport the chart-independent description of derivations
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` — which speaks of
`Γ((U.ι ≫ a)^*Ω_{X/S}, ⊤)` for the affine scheme `U` — to a statement about
`Γ(a^*Ω_{X/S}, U)`, which is what the localization results
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` and
`Stacks.Smooth.isLocalizedModule_conormalRestrict` speak of. That transport is the last missing
ingredient of step (II) of the proof of [Stacks Project, Tag 02H6]; this file supplies it.

The outcome is `Stacks.Smooth.existsUnique_linearMap_of_leibniz_isAffineOpen`: for `U` an
**affine open** of an arbitrary `T`, the sections `Γ(a^*Ω_{X/S}, U)` corepresent the
`Γ(S, V)`-derivations of `Γ(X, W)` over the chart `(V, W)` with values in a `Γ(T, U)`-module.
Stating the transport as a universal property rather than as a bare isomorphism is what makes it
**natural in `U`**: the comparison of two opens is then forced by the uniqueness clause together
with the compatibility `Stacks.Smooth.map_pullbackD` of `pullbackD` with restriction of
sections, so no separate naturality statement is needed.

## Main definitions

* `Stacks.Smooth.restrictSectionsAddEquiv` is the additive equivalence
  `Γ(a^*Ω_{X/S}, U.ι ''ᵁ ⊤) ≃+ Γ((U.ι ≫ a)^*Ω_{X/S}, ⊤)` underlying
  `Stacks.Smooth.restrictPullbackCotangentSheafIso` at the top open.
* `Stacks.Smooth.moduleOfTopIso` is the restriction of scalars of a module over `Γ(U, ⊤)`, for
  `U` an open of a scheme `Y`, to a module over `Γ(Y, U)`.

## Main results

* `Stacks.Smooth.restrictPullbackCotangentSheafIso_unit`: the comparison isomorphism carries the
  unit of `a^* ⊣ a_*`, restricted to `U`, to the unit of `(U.ι ≫ a)^* ⊣ (U.ι ≫ a)_*`.
* `Stacks.Smooth.restrictPullbackCotangentSheafIso_pullbackD`: consequently it carries
  `pullbackD f a W` to `pullbackD f (U.ι ≫ a) W`, over an arbitrary open of `U`. This is the
  compatibility the file is for.
* `Stacks.Smooth.restrictSectionsAddEquiv_smul`: the same map is semilinear over the ring
  isomorphism `Γ(T, U.ι ''ᵁ ⊤) ≅ Γ(U, ⊤)`.
* `Stacks.Smooth.existsUnique_linearMap_of_leibniz`: the chart-independent description of
  derivations with the `Derivation` bundle unfolded into the three defining equations, for `T`
  affine. This is the form that survives transport along a ring isomorphism.
* `Stacks.Smooth.existsUnique_linearMap_of_leibniz_isAffineOpen`: the same over an affine open
  `U` of an arbitrary `T`, which is the statement the Čech step of [Stacks Project, Tag 02H6]
  consumes.
* `Stacks.Smooth.existsUnique_linearMap_of_leibniz_opensTop`: the same with the coefficient
  module given over `Γ(U, ⊤)` and the Leibniz rule written through `U.ι ≫ a`, which is the shape
  in which `Stacks.Smooth.liftDiffDerivation` and `Stacks.Smooth.thickeningKerModule` produce the
  coefficients over a basic open.

## Implementation notes

The unit compatibility is the whole mathematical content, and it is not proved by computing the
comparison isomorphism. That isomorphism is the composite of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, an instance of
`CategoryTheory.Adjunction.leftAdjointUniq`, with
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; both are characterised by their behaviour on
units, the first by `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` and the second by
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` fed into
`CategoryTheory.unit_conjugateEquiv_symm`. The two statements compose to the required identity
once the unit of the composite adjunction is expanded by
`CategoryTheory.Adjunction.comp_unit_app`; the only computation left is that the components of
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` are identities, which holds by `rfl`.

The passage from the unit to `pullbackD` is `Stacks.Smooth.map_pullbackD` together
with the naturality `Stacks.Smooth.app_map_section` of the comparison isomorphism, using that
`Γ(M.restrict U.ι, V) = Γ(M, U.ι ''ᵁ V)` holds on the nose.

Two bookkeeping points govern the shape of the statements.

First, the open that appears naturally is `U.ι ''ᵁ ⊤` rather than `U`: the sections of a
restriction are the sections over the image of the open, and `AlgebraicGeometry.Scheme.Opens.ι`
is *not* an equality of opens but `AlgebraicGeometry.Scheme.Opens.ι_image_top`. Everything is
therefore proved for `U.ι ''ᵁ ⊤`, where the rings `Γ(T, U.ι ''ᵁ ⊤)` and `Γ(U, ⊤)` are the same
type, and rewritten to `U` at the very end. The rewriting is legitimate because the whole
statement depends on the open only.

Second, the universal property is stated with the three defining equations of a derivation
(additivity, vanishing on the base, Leibniz) rather than with a `Derivation`. A `Derivation`
over `Γ(S, V)` with values in `M` carries the `Γ(X, W)`-module structure of
`Stacks.Smooth.moduleOfAppLE` inside its type, so transporting one along the ring isomorphism
`Γ(T, U.ι ''ᵁ ⊤) ≅ Γ(U, ⊤)` would mean transporting a type-class instance; with the equations
spelled out, the transport is `Stacks.Smooth.existsUnique_linearMap_of_ringEquiv`, which moves
only elements. Unbundling costs nothing at the point of use: for the module structures in play
the Leibniz rule of a derivation *is* the displayed equation, by `rfl`.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Modules

/-- The two components of an isomorphism of sheaves of modules are inverse on sections. -/
theorem app_inv_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (V : Y.Opens) (z : Γ(N, V)) :
    (e.hom.app V).hom ((e.inv.app V).hom z) = z :=
  (AlgebraicGeometry.sectionsLinearEquivOfIso e V).apply_symm_apply z

/-- **The restriction of a sheaf of modules to an open subscheme carries the same action.** For
`U` an open of `Y` and `P` a sheaf of modules on `Y`, the sections of `P.restrict U.ι` over `⊤`
are the sections of `P` over `U.ι ''ᵁ ⊤` on the nose, and the action of `Γ(U, ⊤)` on the former
is the action of `Γ(Y, U.ι ''ᵁ ⊤)` on the latter — the two rings also being the same type.

This is `AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` specialised to the inclusion
of an open subscheme, where the comparison ring isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso` is the identity by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`. -/
theorem smul_restrict_top {Y : Scheme.{u}} (U : Y.Opens) (P : Y.Modules)
    (r : Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)))
    (r' : Γ(Y, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (hr : (U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).inv.hom r = r')
    (x : Γ(P.restrict U.ι, (⊤ : (U : Scheme.{u}).Opens))) :
    (Scheme.Modules.restrictAppIso U.ι P ⊤).hom.hom (r • x)
      = r' • (Scheme.Modules.restrictAppIso U.ι P ⊤).hom.hom x := by
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, hr]

end Stacks.Modules

namespace Stacks.Smooth

/-! ### The comparison isomorphism on units -/

section Unit

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (U : T.Opens)

/-- **`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` on units.** The comparison of
restriction along an open immersion with pullback along it carries the unit of
`restrict ⊣ pushforward`, which is restriction of sections, to the unit of
`pullback ⊣ pushforward`. -/
theorem restrictFunctorIsoPullback_app_map (P : T.Modules) (V : T.Opens) (t : Γ(P, V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app P).app (U.ι ⁻¹ᵁ V)
        ((P.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op).hom t)
      = ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app P).app V t := by
  have h := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) P
  exact congr($(h).app V t)

/-- **`AlgebraicGeometry.Scheme.Modules.pullbackComp` on units.** The unit of
`(U.ι ≫ a)^* ⊣ (U.ι ≫ a)_*` at `Ω_{X/S}` is the unit of `a^* ⊣ a_*` followed by the unit of
`U.ι^* ⊣ U.ι_*`, compared along the composition isomorphism of pullbacks.

This is the mate correspondence `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`
read on units by `CategoryTheory.unit_conjugateEquiv_symm`. -/
theorem pullbackComp_app_unit (V : X.Opens) (s : Γ(cotangentSheaf f, V)) :
    ((Scheme.Modules.pullbackComp U.ι a).hom.app (cotangentSheaf f)).app (U.ι ⁻¹ᵁ (a ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
            (pullbackCotangentSheaf f a)).app (a ⁻¹ᵁ V) ((pullbackCotangentUnitApp f a V).hom s))
      = (pullbackCotangentUnitApp f (U.ι ≫ a) V).hom s := by
  have hc : (conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι))
      (Scheme.Modules.pullbackPushforwardAdjunction (U.ι ≫ a))).symm
      (Scheme.Modules.pushforwardComp U.ι a).hom = (Scheme.Modules.pullbackComp U.ι a).inv :=
    (Equiv.symm_apply_eq _).mpr (Scheme.Modules.conjugateEquiv_pullbackComp_inv U.ι a).symm
  have h := CategoryTheory.unit_conjugateEquiv_symm
    ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι))
    (Scheme.Modules.pullbackPushforwardAdjunction (U.ι ≫ a))
    (Scheme.Modules.pushforwardComp U.ι a).hom (cotangentSheaf f)
  rw [hc, CategoryTheory.Adjunction.comp_unit_app] at h
  have h2 := congr($(h).app V s)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforward_map_app] at h2
  rw [show (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
      (pullbackCotangentSheaf f a)).app (a ⁻¹ᵁ V) ((pullbackCotangentUnitApp f a V).hom s)) =
      ((Scheme.Modules.pullbackComp U.ι a).inv.app (cotangentSheaf f)).app
        (U.ι ⁻¹ᵁ (a ⁻¹ᵁ V)) ((pullbackCotangentUnitApp f (U.ι ≫ a) V).hom s) from h2]
  exact Stacks.Modules.app_inv_app
    ((Scheme.Modules.pullbackComp U.ι a).app (cotangentSheaf f)) _ _

/-- **The comparison isomorphism carries the unit of `a^* ⊣ a_*` to the unit of
`(U.ι ≫ a)^* ⊣ (U.ι ≫ a)_*`.** For `V` an open of `X` and `s` a section of `Ω_{X/S}` over `V`,
the image of `s` under the unit of `a^* ⊣ a_*`, restricted to the open `U.ι ⁻¹ᵁ (a ⁻¹ᵁ V)` of
`U`, corresponds under `Stacks.Smooth.restrictPullbackCotangentSheafIso` to the image of `s`
under the unit of `(U.ι ≫ a)^* ⊣ (U.ι ≫ a)_*`. -/
theorem restrictPullbackCotangentSheafIso_unit (V : X.Opens) (s : Γ(cotangentSheaf f, V)) :
    ((restrictPullbackCotangentSheafIso f a U).hom.app (U.ι ⁻¹ᵁ (a ⁻¹ᵁ V))).hom
        (((pullbackCotangentSheaf f a).presheaf.map
            (homOfLE (U.ι.image_preimage_le (a ⁻¹ᵁ V))).op).hom
          ((pullbackCotangentUnitApp f a V).hom s))
      = (pullbackCotangentUnitApp f (U.ι ≫ a) V).hom s := by
  show ((Scheme.Modules.pullbackComp U.ι a).hom.app (cotangentSheaf f)).app
      (U.ι ⁻¹ᵁ (a ⁻¹ᵁ V))
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
          (pullbackCotangentSheaf f a)).app (U.ι ⁻¹ᵁ (a ⁻¹ᵁ V)) _) = _
  rw [restrictFunctorIsoPullback_app_map U (pullbackCotangentSheaf f a) (a ⁻¹ᵁ V)]
  exact pullbackComp_app_unit f a U V s

/-- **The comparison isomorphism carries `pullbackD` to `pullbackD`.** Let `W` be an open of `X`
and `O` an open of `U` carried into `W` by `a`. Then the comparison isomorphism
`Stacks.Smooth.restrictPullbackCotangentSheafIso` sends the pullback along `a` of the universal
differential of a section of `𝒪_X` over `W`, read over `U.ι ''ᵁ O`, to the pullback of the same
universal differential along the restricted morphism `U.ι ≫ a`, read over `O`.

At `O = ⊤` this is the compatibility that lets the chart-independent description of derivations
be transported from `Γ((U.ι ≫ a)^*Ω_{X/S}, ⊤)` to `Γ(a^*Ω_{X/S}, U)`. An arbitrary `O` is what a
derivation datum attached to a lift over `U` needs: such a datum is evaluated on the preimages of
opens of the target, never on the whole of `U`. -/
theorem restrictPullbackCotangentSheafIso_pullbackD {W : X.Opens} {O : (U : Scheme.{u}).Opens}
    (h₀ : U.ι ''ᵁ O ≤ a ⁻¹ᵁ W) (hUW' : O ≤ (U.ι ≫ a) ⁻¹ᵁ W) (b : Γ(X, W)) :
    ((restrictPullbackCotangentSheafIso f a U).hom.app O).hom (pullbackD f a W h₀ b)
      = pullbackD f (U.ι ≫ a) W hUW' b := by
  have hle : U.ι ''ᵁ O ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ (a ⁻¹ᵁ W)) :=
    Scheme.Hom.image_mono U.ι hUW'
  have hz := map_pullbackD f a W (U.ι.image_preimage_le (a ⁻¹ᵁ W)) h₀ hle b
  rw [pullbackD_apply f (U.ι ≫ a) W hUW' b,
    ← restrictPullbackCotangentSheafIso_unit f a U W (universalD f W b),
    ← pullbackD_apply f a W (U.ι.image_preimage_le (a ⁻¹ᵁ W))]
  refine Eq.trans (congrArg
    (fun z : Γ((pullbackCotangentSheaf f a).restrict U.ι, O) ↦
      ((restrictPullbackCotangentSheafIso f a U).hom.app O).hom z) hz.symm) ?_
  exact app_map_section (restrictPullbackCotangentSheafIso f a U).hom hUW'
    (pullbackD f a W (U.ι.image_preimage_le (a ⁻¹ᵁ W)) b)

end Unit

/-! ### The semilinear equivalence on sections -/

section Sections

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (U : T.Opens)

/-- **The sections of `a^*Ω_{X/S}` over the image of `U` are the global sections of
`(U.ι ≫ a)^*Ω_{X/S}`**, as abelian groups. This is
`Stacks.Smooth.restrictPullbackCotangentSheafIso` on sections over the top open, using that the
sections of a restriction along an open immersion are the sections over the image. -/
noncomputable def restrictSectionsAddEquiv :
    Γ(pullbackCotangentSheaf f a, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) ≃+
      Γ(pullbackCotangentSheaf f (U.ι ≫ a), (⊤ : (U : Scheme.{u}).Opens)) where
  toFun := ((restrictPullbackCotangentSheafIso f a U).hom.app ⊤).hom
  map_add' := map_add _
  invFun := ((restrictPullbackCotangentSheafIso f a U).inv.app ⊤).hom
  left_inv x := by
    have h := congrArg (fun φ : (pullbackCotangentSheaf f a).restrict U.ι ⟶
        (pullbackCotangentSheaf f a).restrict U.ι ↦ (φ.app ⊤).hom x)
      (restrictPullbackCotangentSheafIso f a U).hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
    exact h
  right_inv y :=
    Stacks.Modules.app_inv_app (restrictPullbackCotangentSheafIso f a U) ⊤ y

/-- `Stacks.Smooth.restrictSectionsAddEquiv` is semilinear over the comparison ring isomorphism
`Γ(T, U.ι ''ᵁ ⊤) ≅ Γ(U, ⊤)` of `AlgebraicGeometry.Scheme.Hom.appIso`. -/
theorem restrictSectionsAddEquiv_smul
    (r : Γ(T, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (x : Γ(pullbackCotangentSheaf f a, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) :
    restrictSectionsAddEquiv f a U (r • x)
      = (U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).hom.hom r •
        restrictSectionsAddEquiv f a U x := by
  have hr : (U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).inv.hom
      ((U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).hom.hom r) = r :=
    congr($((U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).hom_inv_id).hom r)
  have hsmul := Stacks.Modules.smul_restrict_top U (pullbackCotangentSheaf f a)
    ((U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).hom.hom r) r hr x
  refine Eq.trans (congrArg
    (fun z : Γ((pullbackCotangentSheaf f a).restrict U.ι, (⊤ : (U : Scheme.{u}).Opens)) ↦
      ((restrictPullbackCotangentSheafIso f a U).hom.app ⊤).hom z) hsmul.symm) ?_
  exact Scheme.Modules.Hom.app_smul (restrictPullbackCotangentSheafIso f a U).hom _ x

/-- The sections over `U.ι ''ᵁ ⊤` of the structure sheaf of `T`, read through the comparison ring
isomorphism and then through the restricted morphism, give the sections of `a` over the chart
`W`. -/
theorem appLE_comp_appIso_hom {W : X.Opens}
    (h₀ : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ a ⁻¹ᵁ W)
    (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) :
    a.appLE W (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) h₀ ≫
        (U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).hom
      = (U.ι ≫ a).appLE W (⊤ : (U : Scheme.{u}).Opens) hUW' := by
  rw [Scheme.Hom.appIso_hom' U.ι (⊤ : (U : Scheme.{u}).Opens)]
  exact Scheme.Hom.appLE_comp_appLE U.ι a W (U.ι ''ᵁ ⊤) ⊤ h₀ _

end Sections

/-! ### Transport of the universal property along a ring isomorphism -/

/-- Precomposing an `R'`-linear map with a `ρ`-semilinear additive equivalence is `R`-linear. -/
private theorem exists_linearMap_comp_addEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (ρ : R ≃+* R') {A A' M : Type u} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup M]
    [Module R A] [Module R' A'] [Module R M] [Module R' M]
    (hM : ∀ (r : R) (m : M), r • m = ρ r • m) (e : A ≃+ A')
    (he : ∀ (r : R) (x : A), e (r • x) = ρ r • e x) (θ' : A' →ₗ[R'] M) :
    ∃ θ : A →ₗ[R] M, ∀ x, θ x = θ' (e x) :=
  ⟨{ toFun := fun x ↦ θ' (e x)
     map_add' := fun x y ↦ by rw [map_add, map_add]
     map_smul' := fun r x ↦ by rw [he, map_smul, hM]; rfl }, fun _ ↦ rfl⟩

/-- **A corepresentation statement transports along a ring isomorphism.** Let `ρ : R ≃+* R'` be a
ring isomorphism, let `A` be an `R`-module and `A'` an `R'`-module, let `M` carry both an
`R`-module and an `R'`-module structure with the two actions matching through `ρ`, and let
`e : A ≃+ A'` be semilinear over `ρ`. If a family `d : B → A` corresponds to a family
`d' : B → A'` under `e`, then the `R'`-linear maps `A' → M` extending a given `δ : B → M` along
`d'` are in bijection with the `R`-linear maps `A → M` extending `δ` along `d`; in particular
one exists uniquely as soon as the other does.

This is what carries `Stacks.Smooth.existsUnique_linearMap_of_leibniz` for the affine scheme `U`
over to `Stacks.Smooth.existsUnique_linearMap_of_leibniz_isAffineOpen`. -/
theorem existsUnique_linearMap_of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (ρ : R ≃+* R') {A A' M : Type u} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup M]
    [Module R A] [Module R' A'] [Module R M] [Module R' M]
    (hM : ∀ (r : R) (m : M), r • m = ρ r • m) (e : A ≃+ A')
    (he : ∀ (r : R) (x : A), e (r • x) = ρ r • e x) {B : Type*} (d : B → A) (d' : B → A')
    (hd : ∀ b, e (d b) = d' b) (δ : B → M)
    (h : ∃! θ' : A' →ₗ[R'] M, ∀ b, θ' (d' b) = δ b) :
    ∃! θ : A →ₗ[R] M, ∀ b, θ (d b) = δ b := by
  obtain ⟨θ', hθ', huniq'⟩ := h
  have hsymm : ∀ (r' : R') (y : A'), e.symm (r' • y) = ρ.symm r' • e.symm y := fun r' y ↦ by
    refine e.injective ?_
    rw [he, e.apply_symm_apply, e.apply_symm_apply, ρ.apply_symm_apply]
  obtain ⟨θ₁, h₁⟩ := exists_linearMap_comp_addEquiv ρ hM e he θ'
  refine ⟨θ₁, fun b ↦ by rw [h₁, hd, hθ'], fun θ hθ ↦ ?_⟩
  obtain ⟨θ₂, h₂⟩ := exists_linearMap_comp_addEquiv ρ.symm
    (fun r' m ↦ by rw [hM, ρ.apply_symm_apply]) e.symm hsymm θ
  have hθ₂ : θ₂ = θ' := huniq' _ fun b ↦ by rw [h₂, ← hd b, e.symm_apply_apply, hθ]
  refine LinearMap.ext fun x ↦ ?_
  have hx := LinearMap.congr_fun hθ₂ (e x)
  rw [h₁]
  rwa [h₂, e.symm_apply_apply] at hx

/-! ### The universal property with the derivation axioms spelled out -/

/-- **Derivations at an affine chart are the linear maps out of `Γ(a^*Ω_{X/S}, ⊤)`, with the
derivation axioms spelled out.** Let `V` be an affine open of `S` and `W` an affine open of `X`
with `W ≤ f ⁻¹ᵁ V`, let `T` be affine and `a : T ⟶ X` a morphism mapping into `W`, and let `M` be
a `Γ(T, ⊤)`-module. A map `δ : Γ(X, W) → M` which is additive, kills the sections coming from
`Γ(S, V)` and satisfies the Leibniz rule for the action read through `a.appLE W ⊤` is induced by
exactly one `Γ(T, ⊤)`-linear map `Γ(a^*Ω_{X/S}, ⊤) → M`.

This is `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` with the `Derivation`
bundle replaced by its defining equations, which is what lets the statement be transported along
a ring isomorphism. -/
theorem existsUnique_linearMap_of_leibniz {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)
    {V : S.Opens} {W : X.Opens} [IsAffine T] (M : Type u) [AddCommGroup M]
    [Module Γ(T, (⊤ : T.Opens)) M] (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (δ : Γ(X, W) → M)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hbase : ∀ r : Γ(S, V), δ ((f.appLE V W hWV).hom r) = 0)
    (hleib : ∀ x y, δ (x * y) = (a.appLE W ⊤ hUW).hom x • δ y
      + (a.appLE W ⊤ hUW).hom y • δ x) :
    ∃! θ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] M,
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) = δ b := by
  let := algebraAppLE f hWV
  let := moduleOfAppLE a hUW M
  let := moduleOfAppLEBase f a hWV hUW M
  let := isScalarTowerOfAppLEBase f a hWV hUW M
  refine existsUnique_linearMap_comp_pullbackD_of_module f a M hV hW hWV hUW
    { toFun := δ
      map_add' := hadd
      map_smul' := fun r x ↦ by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hleib, hbase, smul_zero, add_zero]
        rfl
      map_one_eq_zero' := by
        have h := hbase 1
        rwa [map_one] at h
      leibniz' := hleib }

/-- **Derivations at an affine chart are the linear maps out of `Γ(a^*Ω_{X/S}, U)`, for `U` an
affine open of an arbitrary `T`.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine
open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, let `a : T ⟶ X` be a morphism of
schemes, let `U` be an affine open of `T` with `U ≤ a ⁻¹ᵁ W` and let `M` be a `Γ(T, U)`-module.
A map `δ : Γ(X, W) → M` which is additive, kills the sections coming from `Γ(S, V)` and satisfies
the Leibniz rule for the action read through `a.appLE W U` is induced by exactly one
`Γ(T, U)`-linear map `Γ(a^*Ω_{X/S}, U) → M`.

This is the statement that the Čech step (II) of [Stacks Project, Tag 02H6] consumes: the left
side depends on a chart and the right side does not, and — unlike
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`, which needs the *source* of `a`
to be affine — the module of sections it corepresents is a module of sections of one sheaf on one
scheme, so it localizes by
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`.

Naturality in `U` is a consequence of the uniqueness clause: if `U' ≤ U` and `φ : M → M'` is
compatible with the coefficient modules, then `φ ∘ θ_U` and `θ_{U'} ∘ res` both send
`pullbackD f a W b` to `φ (δ b)`, by `Stacks.Smooth.map_pullbackD`, so they agree. -/
theorem existsUnique_linearMap_of_leibniz_isAffineOpen {X S T : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ X) {V : S.Opens} {W : X.Opens} {U : T.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (M : Type u) [AddCommGroup M] [Module Γ(T, U) M] (δ : Γ(X, W) → M)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hbase : ∀ r : Γ(S, V), δ ((f.appLE V W hWV).hom r) = 0)
    (hleib : ∀ x y, δ (x * y) = (a.appLE W U hUW).hom x • δ y
      + (a.appLE W U hUW).hom y • δ x) :
    ∃! θ : Γ(pullbackCotangentSheaf f a, U) →ₗ[Γ(T, U)] M,
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) = δ b := by
  have hUa : IsAffine (U : Scheme.{u}) := hU
  have key : ∀ (O : T.Opens), O = U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) →
      ∀ (N : Type u) (_ : AddCommGroup N) (_ : Module Γ(T, O) N) (h₀ : O ≤ a ⁻¹ᵁ W)
        (ε : Γ(X, W) → N),
      (∀ x y, ε (x + y) = ε x + ε y) → (∀ r : Γ(S, V), ε ((f.appLE V W hWV).hom r) = 0) →
      (∀ x y, ε (x * y) = (a.appLE W O h₀).hom x • ε y + (a.appLE W O h₀).hom y • ε x) →
      ∃! θ : Γ(pullbackCotangentSheaf f a, O) →ₗ[Γ(T, O)] N,
        ∀ b : Γ(X, W), θ (pullbackD f a W h₀ b) = ε b := by
    rintro O rfl N _ _ h₀ ε hadd hbase hleib
    have hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W := by
      intro x _
      show a.base (U.ι.base x) ∈ W
      exact h₀ ⟨x, trivial, rfl⟩
    set ρ := (U.ι.appIso (⊤ : (U : Scheme.{u}).Opens)).commRingCatIsoToRingEquiv
    let : Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) N :=
      Module.compHom N (ρ.symm : Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) →+*
        Γ(T, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    have hM : ∀ (r : Γ(T, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) (m : N), r • m = ρ r • m :=
      fun r m ↦ by
        show r • m = ρ.symm (ρ r) • m
        rw [ρ.symm_apply_apply]
    have hring : ∀ x : Γ(X, W), ρ ((a.appLE W (U.ι ''ᵁ ⊤) h₀).hom x)
        = ((U.ι ≫ a).appLE W (⊤ : (U : Scheme.{u}).Opens) hUW').hom x := fun x ↦ by
      have h := appLE_comp_appIso_hom a U h₀ hUW'
      exact congr($(h).hom x)
    refine existsUnique_linearMap_of_ringEquiv ρ hM (restrictSectionsAddEquiv f a U)
      (restrictSectionsAddEquiv_smul f a U) (fun b ↦ pullbackD f a W h₀ b)
      (fun b ↦ pullbackD f (U.ι ≫ a) W hUW' b)
      (fun b ↦ restrictPullbackCotangentSheafIso_pullbackD f a U h₀ hUW' b) ε
      (existsUnique_linearMap_of_leibniz f (U.ι ≫ a) N hV hW hWV hUW' ε hadd hbase
        fun x y ↦ ?_)
    rw [hleib x y, hM, hM, hring, hring]
  exact key U U.ι_image_top.symm M ‹_› ‹_› hUW δ hadd hbase hleib

/-! ### The same for coefficients given over the open subscheme -/

/-- The `Γ(Y, U)`-module structure on a `Γ(U, ⊤)`-module obtained by restricting scalars along
`AlgebraicGeometry.Scheme.Opens.topIso`. This is the structure that lets a coefficient module
produced on the affine scheme `U` — such as the conormal module
`Stacks.Smooth.thickeningKerModule` of a thickening restricted to a basic open — be read as a
module over the sections of `𝒪_Y` on `U`. -/
@[instance_reducible]
noncomputable def moduleOfTopIso {Y : Scheme.{u}} (U : Y.Opens) (M : Type*) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] : Module Γ(Y, U) M :=
  Module.compHom _ U.topIso.inv.hom

/-- The sections of `a` over a chart `W`, read on an open `U` of the source and then transported
to the open subscheme `U`, are the sections over `W` of the restricted morphism `U.ι ≫ a`. -/
theorem appLE_comp_topIso_inv {X T : Scheme.{u}} (a : T ⟶ X) (U : T.Opens) {W : X.Opens}
    (hUW : U ≤ a ⁻¹ᵁ W) (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) :
    a.appLE W U hUW ≫ U.topIso.inv = (U.ι ≫ a).appLE W (⊤ : (U : Scheme.{u}).Opens) hUW' := by
  rw [← opens_ι_appLE_top (W := U)]
  exact Scheme.Hom.appLE_comp_appLE U.ι a W U ⊤ hUW _

/-- **Derivations at an affine chart are the linear maps out of `Γ(a^*Ω_{X/S}, U)`, with
coefficients over the open subscheme.** This is
`Stacks.Smooth.existsUnique_linearMap_of_leibniz_isAffineOpen` for a coefficient module given as
a module over `Γ(U, ⊤)` rather than over `Γ(T, U)`, and with the Leibniz rule written through the
restricted morphism `U.ι ≫ a`.

That is the shape in which the coefficients actually arise in step (II) of
[Stacks Project, Tag 02H6]: the conormal module of a first-order thickening restricted to a basic
open `D(g)` of `T'` is a module over the global sections of the affine scheme
`i ⁻¹ᵁ D(g)` by `Stacks.Smooth.thickeningKerModule`, and the difference
`Stacks.Smooth.liftDiffDerivation` of two local solutions satisfies the Leibniz rule for the
sections of the restricted morphism. -/
theorem existsUnique_linearMap_of_leibniz_opensTop {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)
    {V : S.Opens} {W : X.Opens} {U : T.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) (M : Type u) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] (δ : Γ(X, W) → M)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hbase : ∀ r : Γ(S, V), δ ((f.appLE V W hWV).hom r) = 0)
    (hleib : ∀ x y, δ (x * y) = ((U.ι ≫ a).appLE W ⊤ hUW').hom x • δ y
      + ((U.ι ≫ a).appLE W ⊤ hUW').hom y • δ x) :
    letI := moduleOfTopIso U M
    ∃! θ : Γ(pullbackCotangentSheaf f a, U) →ₗ[Γ(T, U)] M,
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) = δ b := by
  let := moduleOfTopIso U M
  have hact : ∀ (x : Γ(X, W)) (m : M), (a.appLE W U hUW).hom x • m
      = ((U.ι ≫ a).appLE W (⊤ : (U : Scheme.{u}).Opens) hUW').hom x • m := fun x m ↦ by
    show (U.topIso.inv.hom ((a.appLE W U hUW).hom x)) • m = _
    rw [← CommRingCat.comp_apply, appLE_comp_topIso_inv a U hUW hUW']
  refine existsUnique_linearMap_of_leibniz_isAffineOpen f a hU hV hW hWV hUW M δ hadd hbase
    fun x y ↦ ?_
  rw [hleib x y, hact, hact]

end Stacks.Smooth

end

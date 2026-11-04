module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Kaehler
public import StacksFrontier.AlgebraicGeometry.FromSpecImageTop

/-!
# Stacks 01UT: the sections of the relative differentials on an affine open

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and let
`U ≤ f ⁻¹ᵁ V` be an affine open of `X`. This file proves that the canonical comparison map
`AffineDifferentials.kaehlerToSections` from the Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)`
to the sections of `Ω_{X/S}` on `U` is an isomorphism, and hence Stacks 01UT.

## Main definitions

* `specDifferentials` is the restriction of `Ω_{X/S}` to `Spec Γ(X, U)` along
  `IsAffineOpen.fromSpec`, and `specDerivation` is the universal relative derivation of `f`
  read on the opens of that spectrum.
* `specTopDerivation` is that derivation on the whole spectrum, as a ring-theoretic derivation
  of `Γ(X, U)` relative to `Γ(S, V)`.
* `fromTilde` is the morphism from the quasi-coherent sheaf attached to the Kähler
  differentials back to `specDifferentials`.

## Main results

* `map_injective`: a restriction map of a sheaf of modules between two opens each contained
  in the other is injective.
* `spec_hom_ext`: a morphism out of `specDifferentials` is determined by its effect on
  `specDerivation`.
* `spec_hom_ext_top`: it is determined by its effect on the whole spectrum alone.
* `isIso_kaehlerToSections`: the comparison map is an isomorphism.
* `existsUnique_affineDifferentialsIso`: **Stacks 01UT**, in the form the tag asserts.

## Implementation notes

The route is not the localization argument that the companion file's "what is not done" first
proposed, and not quasi-coherence of `Ω_{X/S}` either. Both are avoided by the following
observation, which makes the uniqueness half of Stacks 01UO do all the work.

Write `k` for `IsAffineOpen.fromSpec`, `M` for the restriction of `Ω_{X/S}` along `k` and `T`
for the quasi-coherent sheaf on `Spec Γ(X, U)` attached to the Kähler differentials. The
morphism `ψ : Ω_{X/S} ⟶ k_* T` of the companion file transposes, across the adjunction between
restriction and pushforward, to `ψ' : M ⟶ T`. A morphism out of `M` is determined by its effect
on the universal relative derivation — that is the universal property of `Ω_{X/S}` read through
the adjunction, `spec_hom_ext` — and the derivation it induces on the opens of `Spec Γ(X, U)`
is a Leibniz, restriction-compatible family on an affine scheme, so by
`DifferentialsAffine.eq_of_eq_on_affineOpen` it is determined by its value on `⊤` alone. That
is `spec_hom_ext_top`, and it means two morphisms out of `M` agree as soon as they agree on
global sections. Since the adjunction between the quasi-coherent sheaf construction and global
sections produces a morphism `fromTilde : T ⟶ M` from the universal relative derivation on `⊤`,
and since `ψ'` carries that derivation to the seed, the composite `ψ' ≫ fromTilde` and the
identity of `M` agree on global sections, hence are equal. Transposing back gives
`ψ ≫ k_* fromTilde = unit`, whose component on `U` is a restriction map between two spellings
of `U`, so injective; therefore `ψ` is injective on sections over `U`, therefore the retraction
of the companion file is injective, and a split monomorphism with injective retraction is an
isomorphism.

The element of `Γ(Spec Γ(X, U), ⊤)` that detects everything is produced by `fromSpec_appLE_top`:
the comorphism of `k` on `U`, restricted to the whole spectrum, is the inverse of the
global-sections comparison. That single identity is what lets the derivation on `⊤` be compared
with the universal relative derivation of a section over `U`, in `specDerivation_top`, and it
is where `IsAffineOpen.fromSpec_app_self` and `IsAffineOpen.fromSpec_preimage_self` are used.

Everything is in a single universe: the schemes are in `Scheme.{u}`, the coordinate ring is in
`CommRingCat.{u}` and the Kähler differentials in `ModuleCat.{u}`, so no universe side
condition arises.

Four transparency points. First, the two opens that have to be identified —
the preimage of `U` with `⊤`, and the image of that preimage with `U` — are compared by
`map_injective` rather than by rewriting an opens equality: both inequalities hold, so the
restriction map has a two-sided inverse built from `Functor.map_comp` and proof irrelevance in
the poset of opens, and no `eqToHom` enters a section type. Second, the chain identifying `ψ'`
on the whole spectrum with the seed is written as six named equalities composed with `Eq.trans`
rather than as a `calc` or a `rw` chain: in `calc` the restriction map of a sheaf of modules
elaborates with its scalars unresolved and the step is rejected for want of a transitivity
instance, and `rw` does not see the naturality pattern because `TopCat.Sheaf` and
`Scheme.Modules` are definitions. Third, after rewriting with `Functor.map_id` the identity
morphism carries the ambient spelling of its object, so `Category.comp_id` has to be applied as
a term; and `Functor.map_id` itself has to be written out with its namespace, since the bare
name resolves to the monad law. Fourth, the inverse of the global-sections comparison is
cancelled by `IsIso.inv_hom_id` as a term rather than by rewriting, since `inv` does not unfold.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

/-! ### Restriction between two spellings of one open -/

/-- A restriction map of a sheaf of modules between two opens each contained in the other is
injective. -/
theorem map_injective {Z : Scheme.{u}} (P : Z.Modules) {W W' : Z.Opens}
    (i : W' ⟶ W) (j : W ⟶ W') : Function.Injective (P.presheaf.map i.op) := by
  have h : ∀ z : Γ(P, W), P.presheaf.map j.op (P.presheaf.map i.op z) = z := by
    intro z
    rw [← CategoryTheory.comp_apply, ← P.presheaf.map_comp,
      show (i.op ≫ j.op) = 𝟙 _ from rfl, P.presheaf.map_id]
    rfl
  exact Function.LeftInverse.injective h

/-! ### The universal derivation read on the spectrum of the coordinate ring -/

section Spec

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U)

/-- The restriction to `Spec Γ(X, U)` of the sheaf of relative differentials of `f`. -/
noncomputable abbrev specDifferentials : (Spec Γ(X, U)).Modules :=
  Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) hU.fromSpec

/-- The universal relative derivation of `f`, read on the opens of `Spec Γ(X, U)`. -/
noncomputable def specDerivation (W : (Spec Γ(X, U)).Opens) :
    Γ(Spec Γ(X, U), W) →+ Γ(specDifferentials f hU, W) :=
  AddMonoidHom.mk'
    (fun z => (Scheme.Hom.universalRelativeDerivation f).d
      ((hU.fromSpec.appIso W).inv.hom z))
    (fun z z' => (congrArg (fun y => (Scheme.Hom.universalRelativeDerivation f).d y)
      (map_add (hU.fromSpec.appIso W).inv.hom z z')).trans (map_add _ _ _))

/-- The derivation on the spectrum satisfies the Leibniz rule. -/
theorem specDerivation_mul (W : (Spec Γ(X, U)).Opens) (z z' : Γ(Spec Γ(X, U), W)) :
    specDerivation f hU W (z * z') =
      z • specDerivation f hU W z' + z' • specDerivation f hU W z :=
  (congrArg (fun y => (Scheme.Hom.universalRelativeDerivation f).d y)
      (map_mul (hU.fromSpec.appIso W).inv.hom z z')).trans
    ((Scheme.Hom.universalRelativeDerivation f).d_mul _ _)

/-- The derivation on the spectrum commutes with the restriction maps. -/
theorem specDerivation_map {W W' : (Spec Γ(X, U)).Opens} (i : W' ⟶ W)
    (z : Γ(Spec Γ(X, U), W)) :
    specDerivation f hU W' ((Spec Γ(X, U)).presheaf.map i.op z) =
      (specDifferentials f hU).presheaf.map i.op (specDerivation f hU W z) := by
  have hnat : (hU.fromSpec.appIso W').inv.hom ((Spec Γ(X, U)).presheaf.map i.op z) =
      X.presheaf.map (hU.fromSpec.opensFunctor.map i).op
        ((hU.fromSpec.appIso W).inv.hom z) :=
    congrArg (fun g => (CommRingCat.Hom.hom g) z)
      (Scheme.Hom.appIso_inv_naturality hU.fromSpec i.op)
  exact (congrArg (fun y => (Scheme.Hom.universalRelativeDerivation f).d y) hnat).trans
    ((Scheme.Hom.universalRelativeDerivation f).d_map
      (hU.fromSpec.opensFunctor.map i).op _)

end Spec


/-! ### Morphisms out of the restriction are determined on the whole spectrum -/

section HomExt

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U)
  {P : (Spec Γ(X, U)).Modules}

/-- The transpose of a morphism out of the restriction, evaluated on the universal relative
differential of a section of the structure sheaf of `X`. -/
theorem homEquiv_d (g : specDifferentials f hU ⟶ P) (W : X.Opens) (a : Γ(X, W)) :
    ((((Scheme.Modules.restrictAdjunction hU.fromSpec).homEquiv
          (Scheme.Hom.relativeDifferentials f) P) g).val.app (op W)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a) =
      (g.val.app (op (hU.fromSpec ⁻¹ᵁ W))).hom
        (specDerivation f hU (hU.fromSpec ⁻¹ᵁ W) ((hU.fromSpec.app W).hom a)) := by
  rw [Adjunction.homEquiv_unit]
  refine congrArg (fun z => (g.val.app (op (hU.fromSpec ⁻¹ᵁ W))).hom z) ?_
  exact ((Scheme.Hom.universalRelativeDerivation f).d_map
      (homOfLE (hU.fromSpec.image_preimage_le W)).op a).symm.trans
    (congrArg (fun z => (Scheme.Hom.universalRelativeDerivation f).d z)
      (congrArg (fun gg => (CommRingCat.Hom.hom gg) a)
        (Scheme.Hom.app_appIso_inv hU.fromSpec W)).symm)

/-- A morphism out of the restriction to the spectrum is determined by its effect on the
universal relative derivation. -/
theorem spec_hom_ext (g g' : specDifferentials f hU ⟶ P)
    (h : ∀ (W : (Spec Γ(X, U)).Opens) (z : Γ(Spec Γ(X, U), W)),
      (g.val.app (op W)).hom (specDerivation f hU W z) =
        (g'.val.app (op W)).hom (specDerivation f hU W z)) :
    g = g' := by
  refine ((Scheme.Modules.restrictAdjunction hU.fromSpec).homEquiv
    (Scheme.Hom.relativeDifferentials f) P).injective ?_
  refine (SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)
    ((Scheme.Modules.pushforward hU.fromSpec).obj P)
    ((Scheme.Hom.universalRelativeDerivation f).postcomp
      (((Scheme.Modules.restrictAdjunction hU.fromSpec).homEquiv
        (Scheme.Hom.relativeDifferentials f) P) g).val)).unique rfl ?_
  apply PresheafOfModules.Derivation.ext
  ext W a
  exact ((homEquiv_d f hU g' W.unop a).trans (h _ _).symm).trans
    (homEquiv_d f hU g W.unop a).symm

/-- A morphism out of the restriction to the spectrum is determined by its effect on the
universal relative derivation over the whole spectrum. This is the uniqueness half of Stacks
01UO doing the work: a Leibniz, restriction-compatible family on the opens of the affine
scheme `Spec Γ(X, U)` is determined by its value on `⊤`. -/
theorem spec_hom_ext_top (g g' : specDifferentials f hU ⟶ P)
    (h : ∀ z : Γ(Spec Γ(X, U), ⊤),
      (g.val.app (op ⊤)).hom (specDerivation f hU ⊤ z) =
        (g'.val.app (op ⊤)).hom (specDerivation f hU ⊤ z)) :
    g = g' := by
  refine spec_hom_ext f hU g g' ?_
  have hmul : ∀ (g : specDifferentials f hU ⟶ P) (W : (Spec Γ(X, U)).Opens)
      (z z' : Γ(Spec Γ(X, U), W)),
      (g.val.app (op W)).hom (specDerivation f hU W (z * z')) =
        z • (id ((g.val.app (op W)).hom (specDerivation f hU W z')) : Γ(P, W)) +
          z' • (id ((g.val.app (op W)).hom (specDerivation f hU W z)) : Γ(P, W)) := by
    intro g W z z'
    rw [specDerivation_mul]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·)
      ((ModuleCat.Hom.hom (g.val.app (op W))).map_smul z _)
      ((ModuleCat.Hom.hom (g.val.app (op W))).map_smul z' _))
  have hres : ∀ (g : specDifferentials f hU ⟶ P) (W W' : (Spec Γ(X, U)).Opens) (hle : W' ≤ W)
      (z : Γ(Spec Γ(X, U), W)),
      (g.val.app (op W')).hom (specDerivation f hU W' ((Spec Γ(X, U)).presheaf.map
        (homOfLE hle).op z)) =
        P.presheaf.map (homOfLE hle).op ((g.val.app (op W)).hom (specDerivation f hU W z)) := by
    intro g W W' hle z
    rw [specDerivation_map]
    exact PresheafOfModules.naturality_apply g.val (homOfLE hle).op _
  have key := DifferentialsAffine.eq_of_eq_on_affineOpen
    (isAffineOpen_top (Spec Γ(X, U)))
    (fun W _ => (ModuleCat.Hom.hom (g.val.app (op W))).toAddMonoidHom.comp
      (specDerivation f hU W))
    (fun W _ => (ModuleCat.Hom.hom (g'.val.app (op W))).toAddMonoidHom.comp
      (specDerivation f hU W))
    (fun W _ => hmul g W) (fun W _ => hmul g' W)
    (fun W W' _ hle => hres g W W' hle) (fun W W' _ hle => hres g' W W' hle)
    (AddMonoidHom.ext h)
  intro W z
  exact DFunLike.congr_fun (congrFun (congrFun key W) le_top) z

end HomExt


/-! ### The derivation on the whole spectrum is the universal relative derivation on `U` -/

section Top

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U)

/-- The comorphism of the canonical morphism from the spectrum, restricted to the whole
spectrum and read back through the comparison of sections, is a restriction map of `X`. -/
theorem appLE_top_appIso_inv :
    hU.fromSpec.appLE U ⊤ (le_of_eq hU.fromSpec_preimage_self.symm) ≫
        (hU.fromSpec.appIso ⊤).inv =
      X.presheaf.map (homOfLE (le_of_eq (hU.fromSpec_image_top))).op := by
  rw [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.appIso_inv_naturality,
    ← Category.assoc, Scheme.Hom.app_appIso_inv]
  exact (X.presheaf.map_comp _ _).symm

/-- On the whole spectrum the derivation is the universal relative derivation of a section
over `U`, restricted. -/
theorem specDerivation_top (a : Γ(X, U)) :
    specDerivation f hU ⊤ ((Scheme.ΓSpecIso Γ(X, U)).inv a) =
      (Scheme.Hom.relativeDifferentials f).presheaf.map
          (homOfLE (le_of_eq (hU.fromSpec_image_top))).op
        ((Scheme.Hom.universalRelativeDerivation f).d a) := by
  have h1 : (hU.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso Γ(X, U)).inv a) =
      X.presheaf.map (homOfLE (le_of_eq (hU.fromSpec_image_top))).op a := by
    refine Eq.trans ?_ (congrArg (fun g => (CommRingCat.Hom.hom g) a)
      (appLE_top_appIso_inv hU))
    exact congrArg (fun y => (hU.fromSpec.appIso ⊤).inv.hom y)
      (congrArg (fun g => (CommRingCat.Hom.hom g) a) (fromSpec_appLE_top hU)).symm
  exact (congrArg (fun y => (Scheme.Hom.universalRelativeDerivation f).d y) h1).trans
    ((Scheme.Hom.universalRelativeDerivation f).d_map
      (homOfLE (le_of_eq (hU.fromSpec_image_top))).op a)

/-- The image of `⊤` under the canonical morphism from the spectrum, written through the
preimage of `U`, is `U`. -/
theorem fromSpec_image_preimage_self :
    hU.fromSpec ''ᵁ (hU.fromSpec ⁻¹ᵁ U) = U := by
  rw [hU.fromSpec_preimage_self, hU.fromSpec_image_top]

end Top


/-! ### The morphism back from the quasi-coherent sheaf -/

section FromTilde

/-- The action of `A` on sections over `⊤` of a sheaf of modules on `Spec A` is the action of
the corresponding section of the structure sheaf. -/
theorem inv_smul_eq {A : CommRingCat.{u}} {M : (Spec A).Modules} (a : A) (x : Γ(M, ⊤)) :
    (Scheme.ΓSpecIso A).inv a • x = a • x :=
  (smul_Spec_top ((Scheme.ΓSpecIso A).inv a) x).symm.trans
    (congrArg (fun z => z • x) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) a))

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
  (hUV : U ≤ f ⁻¹ᵁ V)

/-- The universal relative derivation of `f`, read on the global sections of the restriction
to the spectrum as a ring-theoretic derivation of `Γ(X, U)` relative to `Γ(S, V)`. -/
noncomputable def specTopDerivation :
    (moduleSpecΓFunctor.obj (specDifferentials f hU)).Derivation (f.appLE V U hUV) :=
  ModuleCat.Derivation.mk
    (fun a => specDerivation f hU ⊤ ((Scheme.ΓSpecIso Γ(X, U)).inv a))
    (fun a b => (congrArg (fun y => specDerivation f hU ⊤ y)
        (map_add (CommRingCat.Hom.hom (Scheme.ΓSpecIso Γ(X, U)).inv) a b)).trans
      (map_add (specDerivation f hU ⊤) _ _))
    (fun a b => ((congrArg (fun y => specDerivation f hU ⊤ y)
          (map_mul (CommRingCat.Hom.hom (Scheme.ΓSpecIso Γ(X, U)).inv) a b)).trans
        (specDerivation_mul f hU ⊤ _ _)).trans
      (congrArg₂ (fun p q => p + q) (inv_smul_eq a _) (inv_smul_eq b _)))
    (fun r => (specDerivation_top f hU ((f.appLE V U hUV).hom r)).trans
      ((congrArg (fun y => (Scheme.Hom.relativeDifferentials f).presheaf.map
            (homOfLE (le_of_eq (hU.fromSpec_image_top))).op y)
          (AffineDifferentials.d_appLE_eq_zero f _
            (Scheme.Hom.universalRelativeDerivation f) V U hUV r)).trans (map_zero _)))

/-- The morphism from the quasi-coherent sheaf attached to the Kähler differentials to the
restriction of the relative differentials, furnished by the adjunction between the
quasi-coherent sheaf construction and global sections. -/
noncomputable def fromTilde :
    tilde (kaehlerModule f hUV) ⟶ specDifferentials f hU :=
  (tilde.adjunction.homEquiv (kaehlerModule f hUV) (specDifferentials f hU)).symm
    (specTopDerivation f hU hUV).desc

/-- `fromTilde` on the image of the global-sections comparison is the descent of the
derivation. -/
theorem fromTilde_toTildeTop (m : kaehlerModule f hUV) :
    ((fromTilde f hU hUV).val.app (op ⊤)).hom ((toTildeTop f hUV).hom m) =
      (specTopDerivation f hU hUV).desc.hom m := by
  have h := (tilde.adjunction.homEquiv (kaehlerModule f hUV)
    (specDifferentials f hU)).apply_symm_apply (specTopDerivation f hU hUV).desc
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g => (ModuleCat.Hom.hom g) m) h

/-- `fromTilde` carries the seed to the universal relative derivation on the whole
spectrum. -/
theorem fromTilde_kaehlerSeed (z : Γ(Spec Γ(X, U), ⊤)) :
    ((fromTilde f hU hUV).val.app (op ⊤)).hom (kaehlerSeed f hUV z) =
      specDerivation f hU ⊤ z := by
  rw [show kaehlerSeed f hUV z = (toTildeTop f hUV).hom
      (CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso Γ(X, U)).hom z)) from rfl,
    fromTilde_toTildeTop]
  refine (ModuleCat.Derivation.desc_d (specTopDerivation f hU hUV) _).trans ?_
  exact congrArg (fun y => specDerivation f hU ⊤ y)
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso Γ(X, U)) z)

end FromTilde


/-! ### Stacks 01UT -/

section Main

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
  (hUV : U ≤ f ⁻¹ᵁ V)

/-- The comorphism on `U`, restricted to the whole spectrum, is the global-sections
comparison. -/
theorem map_topToPreimage_app (a : Γ(X, U)) :
    (Spec Γ(X, U)).presheaf.map (topToPreimage hU).op ((hU.fromSpec.app U).hom a) =
      (Scheme.ΓSpecIso Γ(X, U)).inv a :=
  congrArg (fun g => (CommRingCat.Hom.hom g) a) (fromSpec_appLE_top hU)

/-- The unit of the restriction adjunction is the restriction map to the image of the
preimage. -/
theorem restrictAdjunction_unit_app (W : X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentials f, W)) :
    ((((Scheme.Modules.restrictAdjunction hU.fromSpec).unit.app
          (Scheme.Hom.relativeDifferentials f)).val.app (op W)).hom ω) =
      (Scheme.Hom.relativeDifferentials f).presheaf.map
        (homOfLE (hU.fromSpec.image_preimage_le W)).op ω := rfl

include hU in
/-- **Stacks Project, Tag 01UT, existence half.** For `U` and `V` affine, the canonical
comparison map from the Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)` to the sections of
`Ω_{X/S}` on `U` is an isomorphism. -/
theorem isIso_kaehlerToSections (hV : IsAffineOpen V) :
    IsIso (AffineDifferentials.kaehlerToSections f V U hUV) := by
  obtain ⟨E, ψ, hE, hres, hψ⟩ := exists_relativeDifferentials_hom_of_affine f hU hV hUV
    (kaehlerSeed f hUV) (kaehlerSeed_mul f hUV) (kaehlerSeed_base f hU hUV)
  obtain ⟨ψ', hψ'eq⟩ : ∃ q : specDifferentials f hU ⟶ tilde (kaehlerModule f hUV),
      (Scheme.Modules.restrictAdjunction hU.fromSpec).homEquiv
        (Scheme.Hom.relativeDifferentials f) (tilde (kaehlerModule f hUV)) q = ψ :=
    ⟨_, Equiv.apply_symm_apply _ ψ⟩
  have hψ'top : ∀ z : Γ(Spec Γ(X, U), ⊤),
      (ψ'.val.app (op ⊤)).hom (specDerivation f hU ⊤ z) = kaehlerSeed f hUV z := by
    intro z
    have hstar : (ψ'.val.app (op (hU.fromSpec ⁻¹ᵁ U))).hom
          (specDerivation f hU (hU.fromSpec ⁻¹ᵁ U)
            ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z))) =
        E (hU.fromSpec ⁻¹ᵁ U)
          ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z)) := by
      rw [← homEquiv_d f hU ψ' U ((Scheme.ΓSpecIso Γ(X, U)).hom z), hψ'eq]
      exact hψ U ((Scheme.ΓSpecIso Γ(X, U)).hom z)
    have e1 : (Spec Γ(X, U)).presheaf.map (topToPreimage hU).op
        ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z)) = z := by
      rw [map_topToPreimage_app hU, Iso.hom_inv_id_apply]
    have e2 := congrArg (fun y => (ModuleCat.Hom.hom (ψ'.val.app (op ⊤)))
      (specDerivation f hU ⊤ y)) e1
    have e3 := congrArg (fun y => (ModuleCat.Hom.hom (ψ'.val.app (op ⊤))) y)
      (specDerivation_map f hU (topToPreimage hU)
        ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z)))
    have e4 := PresheafOfModules.naturality_apply ψ'.val (topToPreimage hU).op
      (specDerivation f hU (hU.fromSpec ⁻¹ᵁ U)
        ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z)))
    have e5 := congrArg (fun y => (ConcreteCategory.hom
      ((tilde (kaehlerModule f hUV)).presheaf.map (topToPreimage hU).op)) y) hstar
    have e6 := (hres (hU.fromSpec ⁻¹ᵁ U) ⊤ (topToPreimage hU)
      ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z))).symm
    have e7 : E ⊤ ((Spec Γ(X, U)).presheaf.map (topToPreimage hU).op
        ((hU.fromSpec.app U).hom ((Scheme.ΓSpecIso Γ(X, U)).hom z))) =
        kaehlerSeed f hUV z := by
      rw [e1, hE]
    exact ((((e2.symm.trans e3).trans e4).trans e5).trans e6).trans e7
  have hcomp : ψ' ≫ fromTilde f hU hUV = 𝟙 _ := by
    refine spec_hom_ext_top f hU _ _ fun z => ?_
    have h1 : ((ψ' ≫ fromTilde f hU hUV).val.app (op ⊤)).hom (specDerivation f hU ⊤ z) =
        ((fromTilde f hU hUV).val.app (op ⊤)).hom
          ((ψ'.val.app (op ⊤)).hom (specDerivation f hU ⊤ z)) := rfl
    rw [h1, hψ'top z, fromTilde_kaehlerSeed]
    rfl
  have hunit : ψ ≫ (Scheme.Modules.pushforward hU.fromSpec).map (fromTilde f hU hUV) =
      (Scheme.Modules.restrictAdjunction hU.fromSpec).unit.app
        (Scheme.Hom.relativeDifferentials f) := by
    rw [← hψ'eq, ← Adjunction.homEquiv_naturality_right, hcomp, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hψinj : Function.Injective (ModuleCat.Hom.hom (ψ.val.app (op U))) := by
    intro ω ω' hωω'
    have h1 := congrArg (fun m => (ModuleCat.Hom.hom (m.val.app (op U))) ω) hunit
    have h2 := congrArg (fun m => (ModuleCat.Hom.hom (m.val.app (op U))) ω') hunit
    rw [restrictAdjunction_unit_app f hU U ω] at h1
    rw [restrictAdjunction_unit_app f hU U ω'] at h2
    refine map_injective (Scheme.Hom.relativeDifferentials f)
      (homOfLE (hU.fromSpec.image_preimage_le U))
      (homOfLE (le_of_eq (fromSpec_image_preimage_self hU).symm)) ?_
    refine h1.symm.trans (Eq.trans ?_ h2)
    exact congrArg (fun y => (ModuleCat.Hom.hom ((fromTilde f hU hUV).val.app
      (op (hU.fromSpec ⁻¹ᵁ U)))) y) hωω'
  have hd2 : ∀ b : Γ(X, U), (tilde (kaehlerModule f hUV)).presheaf.map (topToPreimage hU).op
        ((ψ.val.app (op U)).hom ((Scheme.Hom.universalRelativeDerivation f).d b)) =
      (toTildeTop f hUV).hom (CommRingCat.KaehlerDifferential.d b) := by
    intro b
    rw [hψ U b, ← hres (hU.fromSpec ⁻¹ᵁ U) ⊤ (topToPreimage hU), hE]
    exact congrArg (fun z => (toTildeTop f hUV).hom
        (CommRingCat.KaehlerDifferential.d (f := f.appLE V U hUV) z))
      (ΓSpecIso_hom_appLE_top hU b)
  have hinvhom : ∀ x, (toTildeTop f hUV).hom ((inv (toTildeTop f hUV)).hom x) = x := fun x =>
    congrArg (fun m => (ModuleCat.Hom.hom m) x) (IsIso.inv_hom_id (toTildeTop f hUV))
  have hretinj : Function.Injective (ModuleCat.Hom.hom (kaehlerRetraction f hU hUV)) := by
    intro x y hxy
    rw [kaehlerRetraction_apply, kaehlerRetraction_apply] at hxy
    have h3 : (tilde (kaehlerModule f hUV)).presheaf.map (topToPreimage hU).op x =
        (tilde (kaehlerModule f hUV)).presheaf.map (topToPreimage hU).op y :=
      (hinvhom _).symm.trans
        ((congrArg (fun w => (toTildeTop f hUV).hom w) hxy).trans (hinvhom _))
    exact map_injective (tilde (kaehlerModule f hUV)) (topToPreimage hU)
      (homOfLE (le_top : hU.fromSpec ⁻¹ᵁ U ≤ ⊤)) h3
  have key : ∀ b : Γ(X, U), (kaehlerRetraction f hU hUV).hom ((ψ.val.app (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b)) =
      CommRingCat.KaehlerDifferential.d b := fun b =>
    (kaehlerRetraction_apply f hU hUV _).trans
      ((congrArg (fun z => (inv (toTildeTop f hUV)).hom z) (hd2 b)).trans
        (congrArg (fun g => (ModuleCat.Hom.hom g) (CommRingCat.KaehlerDifferential.d b))
          (IsIso.hom_inv_id (toTildeTop f hUV))))
  have hsplit : AffineDifferentials.kaehlerToSections f V U hUV ≫
      (ψ.val.app (op U) ≫ kaehlerRetraction f hU hUV) = 𝟙 _ := by
    refine CommRingCat.KaehlerDifferential.ext fun b => ?_
    exact (congrArg (fun z => (kaehlerRetraction f hU hUV).hom ((ψ.val.app (op U)).hom z))
      (AffineDifferentials.kaehlerToSections_d f V U hUV b)).trans (key b)
  refine ⟨ψ.val.app (op U) ≫ kaehlerRetraction f hU hUV, hsplit, ?_⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun ω => ?_)
  refine hretinj.comp hψinj ?_
  exact congrArg (fun g => (ModuleCat.Hom.hom g)
    ((kaehlerRetraction f hU hUV).hom ((ψ.val.app (op U)).hom ω))) hsplit

include hU in
/-- **Stacks Project, Tag 01UT.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be an
affine open of `S` and let `U ≤ f ⁻¹ᵁ V` be an affine open of `X`. The sections of the sheaf
of relative differentials of `f` on `U` are *uniquely* isomorphic to the Kähler differentials
of `Γ(S, V) ⟶ Γ(X, U)`, compatibly with the universal derivations. -/
@[stacks 01UT]
theorem existsUnique_affineDifferentialsIso (hV : IsAffineOpen V) :
    ∃! e : (Scheme.Hom.relativeDifferentials f).val.obj (.op U) ≅
        CommRingCat.KaehlerDifferential (f.appLE V U hUV),
      ∀ a : Γ(X, U), e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
        CommRingCat.KaehlerDifferential.d a :=
  (AffineDifferentials.existsUnique_affineDifferentialsIso_iff_isIso f V U hUV).mpr
    (isIso_kaehlerToSections f hU hUV hV)

end Main

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end

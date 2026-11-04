module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FiniteTypePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Transferring flatness over a base along isomorphisms, open immersions and finite morphisms

This file collects the elementary transfers of the relative flatness predicate
`AlgebraicGeometry.IsFlatOverAt` which the proof of Stacks Tag 05KT needs, together with the
geometric input that an affine chart of a morphism locally of finite type embeds as a closed
subscheme of affine space over an affine open of the base.

## Main results

* `AlgebraicGeometry.ElementaryEtaleFlatness.flatOverAt_iff_of_iso`: relative flatness at a point
  is invariant under isomorphism of modules.
* `AlgebraicGeometry.ElementaryEtaleFlatness.flatOverAt_iff_schemePullback`: relative flatness at
  a point of an open subscheme is relative flatness of the restricted module.
* `AlgebraicGeometry.ElementaryEtaleFlatness.flatOverAt_iff_closedPushforward`: relative flatness
  is insensitive to the direct image along a finite morphism with a one-point fibre.
* `AlgebraicGeometry.ElementaryEtaleFlatness.exists_finiteTypeAffineClosedImmersion`: an affine
  chart of a morphism locally of finite type is a closed subscheme of affine space over the base.

## Implementation notes

The module structure on the stalk of a sheaf of modules comes from the scoped instance
`Stacks.ModuleStalk.stalkModule`, which names Mathlib's construction at the spelling instance
search needs, and the transfers are proved by exhibiting a semilinear equivalence of stalks
(`Stacks.ModuleStalk.equivOfIso`) and appealing to `Module.Flat.equiv_iff`. This file is kept
separate from the proof of Tag 05KT so that the stalk module structure is elaborated without the
competing instance on `Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk` that the import
closure of Tag 05I5 carries.

## References

* [Stacks Project, Tag 05B3](https://stacks.math.columbia.edu/tag/05B3)
* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ElementaryEtaleFlatness

open AlgebraicGeometry

open scoped Stacks.ModuleStalk

universe u

/-- **An affine chart of a morphism locally of finite type.** A point of the source lies in an
affine open mapping into an affine open of the target, on which the morphism induces a ring map
of finite type. -/
lemma exists_affineChart_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    ∃ (U : S.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V hVU).hom.FiniteType := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let U : S.affineOpens := ⟨U₀, hU₀⟩
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U.1).2
  let V : X.affineOpens := ⟨V₀, hV₀⟩
  exact ⟨U, V, hxV, hVU, f.finiteType_appLE U.2 V.2 hVU⟩

/-- Flatness over `R` is transported along a semilinear equivalence of modules, when the `R`-module
structures are restricted along compatible ring maps. -/
private theorem flat_compHom_iff_of_semilinearEquiv {R A B M N : Type*} [CommRing R] [CommRing A]
    [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (ρ : R →+* A) (τ : R →+* B) (σ : A →+* B) (h : σ.comp ρ = τ) (e : M ≃+ N)
    (he : ∀ (a : A) (m : M), e (a • m) = σ a • e m) :
    @Module.Flat R M _ _ (Module.compHom M ρ) ↔ @Module.Flat R N _ _ (Module.compHom N τ) :=
  letI := Module.compHom M ρ
  letI := Module.compHom N τ
  Module.Flat.equiv_iff
    { e with
      map_smul' := fun r m => by
        change e (ρ r • m) = τ r • e m
        rw [he, ← h]
        rfl }

/-- Flatness over the base of the direct image of a quasi-coherent module along a finite
morphism `i`, at a point `i z` whose fibre is the single point `z`, is flatness over the base
of the module itself at `z`: the stalk of the direct image at `i z` is the stalk of the module
at `z` as a module over the base. -/
theorem flatOverAt_iff_closedPushforward
    {Z Y S : Scheme.{u}} (i : Z ⟶ Y) [IsFinite i]
    (q : Y ⟶ S) (G : Z.Modules) [G.IsQuasicoherent]
    (z : Z) (hfiber : i ⁻¹' ({i z} : Set Y) = {z}) :
    AlgebraicGeometry.IsFlatOverAt q.toLRSHom.toShHom
        ((Scheme.Modules.pushforward i).obj G) (i z) ↔
      AlgebraicGeometry.IsFlatOverAt (i ≫ q).toLRSHom.toShHom G z := by
  let R : Type u := S.presheaf.stalk (q (i z))
  let A : Type u := Y.presheaf.stalk (i z)
  let M₁ : PresheafOfModules.{u}
    (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
      ((Scheme.Modules.pushforward i).obj G).val
  let M₂ : PresheafOfModules.{u}
    (Z.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
  let ρ : R →+* A := (q.stalkMap (i z)).hom
  let σ : A →+* Z.presheaf.stalk z := (i.stalkMap z).hom
  let τ : R →+* Z.presheaf.stalk z := ((i ≫ q).stalkMap z).hom
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₁.presheaf (i z)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) ((Scheme.Modules.pushforward i).obj G).val (i z)
  let : Module (Z.presheaf.stalk z)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₂.presheaf z) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) G.val z
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₂.presheaf z) :=
    Module.compHom _ σ
  let : Module R (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₁.presheaf (i z)) :=
    Module.compHom _ ρ
  let : Module R (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₂.presheaf z) :=
    Module.compHom _ τ
  have hmaps : σ.comp ρ = τ := by
    dsimp [τ, σ, ρ]
    exact congrArg (fun φ => φ.hom) (Scheme.Hom.stalkMap_comp i q z).symm
  obtain ⟨e⟩ :=
    AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
      i z hfiber G
  show Module.Flat R (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₁.presheaf (i z)) ↔
    Module.Flat R (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₂.presheaf z)
  let e' : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₁.presheaf (i z)) ≃ₗ[A]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M₂.presheaf z) := e.toLinearEquiv.symm
  exact flat_compHom_iff_of_semilinearEquiv ρ τ σ hmaps e'.toAddEquiv e'.map_smul

/-- The direct image of a finite type quasi-coherent module along a finite morphism is of
finite type, by Stacks Tag 05B3. -/
theorem pushforward_isFiniteType_of_isFinite
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsFinite i]
    (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ((Scheme.Modules.pushforward i).obj G).IsFiniteType :=
  (AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType i G).mp inferInstance

/-- Flatness over the base at a point only depends on the isomorphism class of the module. -/
theorem flatOverAt_iff_of_iso
    {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules}
    (e : F ≅ G) (x : X) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x ↔
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom G x := by
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (S.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  show Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x) ↔
    Module.Flat (S.presheaf.stalk (f x)) (G.presheaf.stalk x)
  let e' := Stacks.ModuleStalk.equivOfIso e x
  exact flat_compHom_iff_of_semilinearEquiv (f.stalkMap x).hom (f.stalkMap x).hom
    (RingHom.id _) (RingHom.id_comp _) e'.toAddEquiv e'.map_smul

/-- The inverse image of a module along a morphism of schemes is the inverse image along the
underlying morphism of sheafed spaces. -/
theorem modulePullback_eq_schemePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj F =
      (Scheme.Modules.pullback f).obj F := rfl

/-- Flatness over the base at a point of an open subscheme is flatness of the restricted
module over the base at the corresponding point, because an open immersion is flat. -/
theorem flatOverAt_iff_schemePullback
    {W X S : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (F : X.Modules) (w : W) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F (j w) ↔
      AlgebraicGeometry.IsFlatOverAt (j ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback j).obj F) w := by
  simpa only [modulePullback_eq_schemePullback] using
    AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt j f F w
      (Flat.stalkMap j w)

/-- **Embedding an affine chart into affine space over the base.** For a morphism locally of
finite type and a point `x` of its source there are affine opens `U ∋ f x` of the target and
`V ∋ x` of the source with `V ⊆ f ⁻¹ U`, an `n`, and a factorisation of `V ⟶ X ⟶ S` as a closed
immersion of `V` into `𝐀ⁿ` over `Γ(S, U)` followed by a morphism locally of finite
presentation to `S`. -/
lemma exists_finiteTypeAffineClosedImmersion {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    ∃ (U : S.affineOpens) (V : X.affineOpens) (_hx : x ∈ V.1)
      (_hVU : V.1 ≤ f ⁻¹ᵁ U.1) (n : ℕ)
      (i : V.1.toScheme ⟶ Spec (.of (MvPolynomial (Fin n) Γ(S, U))))
      (p : Spec (.of (MvPolynomial (Fin n) Γ(S, U))) ⟶ S),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation p ∧ i ≫ p = V.1.ι ≫ f := by
  obtain ⟨U, V, hx, hVU, hft⟩ := exists_affineChart_finiteType f x
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  let R := Γ(S, U)
  let B := Γ(X, V)
  let : Algebra R B := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra.FiniteType R B := hft
  obtain ⟨n, ψ, hψ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let P := MvPolynomial (Fin n) R
  let A := Spec (.of P)
  let i : V.1.toScheme ⟶ A := hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let p : A ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R P)) ≫ hU.fromSpec
  have hi : IsClosedImmersion i :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      hV.isoSpec.hom (Spec.map (CommRingCat.ofHom ψ.toRingHom))).mpr
        (IsClosedImmersion.spec_of_surjective _ hψ)
  have hp : LocallyOfFinitePresentation p := by
    have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
      rw [LocallyOfFinitePresentation.SpecMap_iff]
      simp only [CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
      infer_instance
    have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    dsimp [p]
    infer_instance
  have hcomp : i ≫ p = V.1.ι ≫ f := by
    dsimp [i, p, A, P]
    have hc : ψ.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) =
        (f.appLE U.1 V.1 hVU).hom := by
      ext r
      show ψ (algebraMap R (MvPolynomial (Fin n) R) r) = algebraMap R B r
      rw [ψ.commutes r]
    calc
      (hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))) ≫ hU.fromSpec) =
        hV.isoSpec.hom ≫
          (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R)))) ≫
            hU.fromSpec := by
        simp [Category.assoc]
      _ = hV.isoSpec.hom ≫ Spec.map (f.appLE U.1 V.1 hVU) ≫ hU.fromSpec := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
        simp only [CommRingCat.ofHom_hom]
      _ = V.1.ι ≫ f := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc,
          hV.isoSpec_hom_fromSpec]
  exact ⟨U, V, hx, hVU, n, i, p, hi, hp, hcomp⟩

end AlgebraicGeometry.ElementaryEtaleFlatness

end

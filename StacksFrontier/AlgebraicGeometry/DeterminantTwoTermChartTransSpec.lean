module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTrans

/-!
# The chart comparison of the determinant on the spectra is transitive

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ V' ≤ W` affine opens of `X`. The chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso` identifies the pullback along
`Spec ρ : Spec Γ(X, V) ⟶ Spec Γ(X, W)` of the determinant of `L` on the chart of `W` with the
determinant of `L` on the chart of `V`. This file proves that the comparison composes along a
chain of two inclusions: pulling back to `Spec Γ(X, V')` and then to `Spec Γ(X, V)` agrees with
pulling back to `Spec Γ(X, V)` in one step, read through the factorisation
`AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso` of the pullback.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_trans`: **the chart comparison of
  the determinant on the spectra composes.**

The comparison is the affine pullback comparison of [Stacks, Tag 01I9] followed by the associated
sheaf of the comparison over the rings, so the proof needs the two halves to compose; each is
recorded in the form a chain of inclusions of affine opens produces, namely along a
*factorisation* of the restriction of functions rather than at a literal composite:

* `AlgebraicGeometry.DeterminantTwoTerm.extendScalarsCompOf`: `ModuleCat.extendScalarsComp`
  along a factorisation `ψ ∘ φ = χ` of ring homomorphisms, together with
  `extendScalarsCompOf_app_hom`, which identifies its component with the cancellation
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
* `AlgebraicGeometry.DeterminantTwoTerm.specCompFunIso` and
  `AlgebraicGeometry.DeterminantTwoTerm.pullbackTildeIso_app_comp_of_eq`: the factorisation of
  the pullback along `Spec χ` and the composition compatibility
  `AlgebraicGeometry.pullbackTildeIso_app_comp` of [Stacks, Tag 01I9] read along it.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_trans_hom`: the cocycle
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_trans` over the rings, as an identity
  of morphisms of modules rather than of linear maps.

## Implementation notes

The spelling obstruction of this file is the one recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartNaturalSheaf`.
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso` of a transported
`rfl`, and here it is transported along an equality — `specMap_chartRestriction_comp` — whose two
sides are not syntactically equal, so the transport can never reduce. The two spellings
`((Scheme.Modules.pullbackCongr p).app M).hom` and
`CategoryTheory.NatTrans.app (Scheme.Modules.pullbackCongr p).hom M` are then one iota step apart
and the kernel does not finish it: in this file every statement that puts the `hom` of such a
component next to a component of such a `hom` — including an innocent-looking `rfl` between the
two — fails with `(kernel) deterministic timeout`, while the same statement with the component
left as an *isomorphism* checks in seconds, and raising the heartbeat budget is not an option
available in this repository.

The whole structural half is therefore run on isomorphisms, and at the level of *functors*
wherever possible. `specCompFunIso` names the factorisation of the pullback as a natural
isomorphism, `specCompFunIso_trans` cancels it against
`AlgebraicGeometry.pullbackSpecMapCompIso` without ever evaluating either at a module, and
`chartSpecPullbackCompIso_eq_app` identifies the existing
`AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso` with its component — an equality
of isomorphisms, deliberately not of their `hom`s. Only `specChaseIso` descends to morphisms, and
it does so with every category, functor, object and isomorphism a variable, so that the single
iota step happens once, on variables, where it is free; the concrete comparisons reach it as
explicit arguments and the remaining definitional slack is absorbed by the plain defeq check of
application at default transparency. `natComp`, `isoAppTrans`, `isoAppRefl`, `isoAppCongr`,
`isoCancelLeft`, `transCongrLeft`, `hom_comp_three`, `linComp_congr` and
`eq_inv_comp_of_hom_comp` are the single steps, each closed over variables for the same reason.

The same device gives the two elementwise bridges over the rings: `baseChangeHom_ext` compares
two `B`-linear maps out of `B ⊗[R] N` on the elements `1 ⊗ₜ m` with `N` a variable *type*,
because `TensorProduct.induction_on` run directly on an element of
`↑((ModuleCat.extendScalars χ).obj M)` rewrites the type into a spelling at which the goal is no
longer type-correct under `implicit` transparency and every subsequent rewrite fails.

Transport along a factorisation is by `subst`, in the manner of
`TwoTermDeterminant.baseChangeCompIsoOf` and
`AlgebraicGeometry.DeterminantTwoTerm.specDerivedPullbackCompOf`; equalities are `Prop`s, so
proof irrelevance makes the transported structures definitionally equal to the untransported ones
once the factorisation has been substituted.

The shared universe is imposed by Mathlib's `tilde.functor` and the scheme-module API; the
statements hold in every such universe.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Lemma 26.7.3 (Tag 01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule (cancelBaseChange)

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Formal steps on variables -/

/-- The component at an object of a composite of natural isomorphisms. Isolated so that the step
is taken where the two spellings of a component are one free iota reduction apart. -/
private theorem isoAppTrans {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D} (A : F ≅ G)
    (B : G ≅ H) (N : C) : (A ≪≫ B).app N = A.app N ≪≫ B.app N :=
  rfl

/-- The component at an object of the identity natural isomorphism. -/
private theorem isoAppRefl {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (N : C) :
    (Iso.refl F).app N = Iso.refl (F.obj N) :=
  rfl

/-- Two equal natural isomorphisms have equal components. -/
private theorem isoAppCongr {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} {A B : F ≅ G}
    (N : C) (hAB : A = B) : A.app N = B.app N :=
  congrArg (fun z => z.app N) hAB

/-- Two equal isomorphisms before a fixed one. -/
private theorem transCongrLeft {D : Type*} [Category D] {x y z : D} {e e' : x ≅ y} (t : y ≅ z)
    (he : e = e') : e ≪≫ t = e' ≪≫ t :=
  congrArg (fun u => u ≪≫ t) he

/-- An isomorphism cancelled against the first factor of a composite. -/
private theorem isoCancelLeft {D : Type*} [Category D] {x y : D} (P : x ≅ y) (Q : y ≅ x)
    {t : D} {ρ : x ≅ t} {μ : y ≅ t} (hPQ : P ≪≫ Q = Iso.refl x) (hμ : μ = Q ≪≫ ρ) :
    P ≪≫ μ = ρ := by
  subst hμ
  rw [← Iso.trans_assoc, hPQ, Iso.refl_trans]

/-- The naturality square of a natural transformation between two composites of functors, at a
fixed pair of objects. Isolated so that the components are the ones a consumer holds rather than
the ones the source and target of the morphism dictate. -/
private theorem natComp {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
    (Pg : ℬ ⥤ 𝒟) (TS : 𝒜 ⥤ ℬ) (TT : 𝒞 ⥤ 𝒟) (Eg : 𝒜 ⥤ 𝒞) (α : TS ⋙ Pg ⟶ Eg ⋙ TT)
    (p q : 𝒜) (a : p ⟶ q) :
    Pg.map (TS.map a) ≫ α.app q = α.app p ≫ TT.map (Eg.map a) :=
  α.naturality a

/-- Two `B`-linear maps out of `B ⊗[R] N` agreeing on the elements `1 ⊗ₜ m` are equal. The
source and target are variable *types* rather than objects of `ModuleCat`: running
`TensorProduct.induction_on` on an element of `↑((ModuleCat.extendScalars χ).obj M)` rewrites the
type into a spelling at which the goal is no longer type-correct under `implicit`
transparency. -/
private theorem baseChangeHom_ext {R B N P : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module B P] (F G : (B ⊗[R] N) →ₗ[B] P)
    (h : ∀ m : N, F ((1 : B) ⊗ₜ[R] m) = G ((1 : B) ⊗ₜ[R] m)) : F = G := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul b m => rw [TensorProduct.tmul_eq_smul_one_tmul b m, map_smul, map_smul, h m]

/-- The underlying linear map of a three-fold composite of morphisms of modules. -/
private theorem hom_comp_three {R : Type u} [Ring R] {M N P Q : ModuleCat.{u} R} (x : M ⟶ N)
    (y : N ⟶ P) (z : P ⟶ Q) :
    ModuleCat.Hom.hom (x ≫ y ≫ z) =
      ModuleCat.Hom.hom z ∘ₗ ModuleCat.Hom.hom y ∘ₗ ModuleCat.Hom.hom x :=
  rfl

/-- Two equal pairs of linear maps after a fixed one. Isolated so that the two equalities are
transported with no rewriting inside the composite. -/
private theorem linComp_congr {R : Type u} [CommRing R] {M N P Q : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (u : P →ₗ[R] Q) {v v' : N →ₗ[R] P} {w w' : M →ₗ[R] N} (hv : v = v')
    (hw : w = w') : u ∘ₗ v ∘ₗ w = u ∘ₗ v' ∘ₗ w' := by
  rw [hv, hw]

/-- A morphism precomposed with the component of an isomorphism of functors, read as that
morphism after the inverse component. -/
private theorem eq_inv_comp_of_hom_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) (Y : C) {Z : D} {m : G.obj Y ⟶ Z} {n : F.obj Y ⟶ Z}
    (hn : α.hom.app Y ≫ m = n) : m = α.inv.app Y ≫ n := by
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-! ### Extension of scalars along a factorisation -/

section Rings

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] {B : Type u} [CommRing B]

/-- **The composition isomorphism of extension of scalars along a factorisation.** For ring
homomorphisms `φ : R →+* A`, `ψ : A →+* B` and `χ : R →+* B` with `ψ ∘ φ = χ`, extending scalars
along `χ` is extending scalars along `φ` and then along `ψ`. This is
`ModuleCat.extendScalarsComp`, transported along the factorisation. -/
def extendScalarsCompOf (φ : R →+* A) (ψ : A →+* B) (χ : R →+* B) (hχ : ψ.comp φ = χ) :
    ModuleCat.extendScalars χ ≅
      ModuleCat.extendScalars φ ⋙ ModuleCat.extendScalars ψ := by
  subst hχ
  exact ModuleCat.extendScalarsComp.{u, u} φ ψ

/-- **The composition isomorphism of extension of scalars is the cancellation of a base change.**
The component of `AlgebraicGeometry.DeterminantTwoTerm.extendScalarsCompOf` at an `R`-module `M`
is the inverse of `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which is the shape the
chart comparison of determinants over the rings is stated in.

Both maps are `B`-linear on `B ⊗[R] M`, so it is enough to compare them on the elements
`1 ⊗ₜ m`, where `ModuleCat.extendScalarsComp_hom_app_one_tmul` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul` both give `1 ⊗ₜ 1 ⊗ₜ m`. -/
theorem extendScalarsCompOf_app_hom (φ : R →+* A) (ψ : A →+* B) (χ : R →+* B)
    (hχ : ψ.comp φ = χ) (M : ModuleCat.{u} R) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := χ.toAlgebra
    haveI : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hχ r).symm
    ModuleCat.Hom.hom ((extendScalarsCompOf φ ψ χ hχ).hom.app M) =
      (cancelBaseChange R A B B (M : Type u)).symm.toLinearMap := by
  subst hχ
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine baseChangeHom_ext (R := R) (B := B) (N := (M : Type u))
    (P := B ⊗[A] (A ⊗[R] (M : Type u))) _ _ fun m => ?_
  exact (ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ M m).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R A B 1 m).symm

/-- **Extension of scalars is base change of linear maps.** The image under
`ModuleCat.extendScalars ψ` of a morphism of `A`-modules is `LinearMap.baseChange` of the
underlying linear map. -/
theorem extendScalars_map_hom (ψ : A →+* B) {M N : ModuleCat.{u} A} (l : M ⟶ N) :
    letI : Algebra A B := ψ.toAlgebra
    ModuleCat.Hom.hom ((ModuleCat.extendScalars ψ).map l) =
      LinearMap.baseChange B (ModuleCat.Hom.hom l) := by
  let : Algebra A B := ψ.toAlgebra
  refine baseChangeHom_ext (R := A) (B := B) (N := (M : Type u)) (P := B ⊗[A] (N : Type u)) _ _
    fun m => ?_
  exact (ModuleCat.ExtendScalars.map_tmul ψ l 1 m).trans
    (LinearMap.baseChange_tmul (ModuleCat.Hom.hom l) 1 m).symm

end Rings

/-! ### The affine pullback comparison along a factorisation -/

/-- The comparison of the pullbacks along two morphisms of schemes, at a proof that a morphism is
equal to itself, is the identity. -/
private theorem pullbackCongr_eq_refl {Y Z : Scheme.{u}} {p : Y ⟶ Z} (hp : p = p) :
    Scheme.Modules.pullbackCongr hp = Iso.refl _ :=
  rfl

/-- The comparisons of the pullbacks along two equal morphisms of schemes, in the two directions,
cancel. -/
private theorem pullbackCongr_trans {Y Z : Scheme.{u}} {p q : Y ⟶ Z} (hpq : p = q)
    (hqp : q = p) :
    Scheme.Modules.pullbackCongr hpq ≪≫ Scheme.Modules.pullbackCongr hqp = Iso.refl _ := by
  subst hpq
  rw [pullbackCongr_eq_refl, Iso.refl_trans]

/-- **The factorisation of the pullback along `Spec χ`, for a factorisation of `χ`.** For ring
homomorphisms `f : R ⟶ S`, `g : S ⟶ T` and `k : R ⟶ T` whose spectra factor as
`Spec g ≫ Spec f = Spec k`, pulling back along `Spec f` and then along `Spec g` is pulling back
along `Spec k`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackComp` at the factorisation; it is the
functor-level form of `AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso`. -/
def specCompFunIso {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (hs : Spec.map g ≫ Spec.map f = Spec.map k) :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map k) :=
  Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫ Scheme.Modules.pullbackCongr hs

/-- **The two factorisations of the pullback along `Spec (f ≫ g)` are inverse.**
`AlgebraicGeometry.DeterminantTwoTerm.specCompFunIso` at the composite cancels against
`AlgebraicGeometry.pullbackSpecMapCompIso`.

Both are composites of `AlgebraicGeometry.Scheme.Modules.pullbackComp` with a
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, so the two comparisons cancel by
`pullbackCongr_trans` and the two copies of `pullbackComp` by
`CategoryTheory.Iso.self_symm_id`. The statement is about functors: evaluating either side at a
module is what the kernel cannot afford. -/
theorem specCompFunIso_trans {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (hs : Spec.map g ≫ Spec.map f = Spec.map (f ≫ g)) :
    specCompFunIso f g (f ≫ g) hs ≪≫ pullbackSpecMapCompIso R S T f g = Iso.refl _ := by
  have e : pullbackSpecMapCompIso R S T f g =
      Scheme.Modules.pullbackCongr (Spec.map_comp f g) ≪≫
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).symm := rfl
  have e' : specCompFunIso f g (f ≫ g) hs =
      Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
        Scheme.Modules.pullbackCongr hs := rfl
  rw [e, e', Iso.trans_assoc, ← Iso.trans_assoc (Scheme.Modules.pullbackCongr hs),
    pullbackCongr_trans, Iso.refl_trans, Iso.self_symm_id]

/-- **The affine pullback comparison of [Stacks, Tag 01I9] composes along a factorisation.** For
ring homomorphisms `f : R ⟶ S`, `g : S ⟶ T` and `k : R ⟶ T` with `f ≫ g = k` and an `R`-module
`M`, the factorisation `AlgebraicGeometry.DeterminantTwoTerm.specCompFunIso` of the pullback
along `Spec k`, followed by the comparison for `k` at `M`, is the pullback along `Spec g` of the
comparison for `f`, followed by the comparison for `g` at `S ⊗_R M`, followed by the associated
sheaf of the inverse of `AlgebraicGeometry.DeterminantTwoTerm.extendScalarsCompOf`.

This is `AlgebraicGeometry.pullbackTildeIso_app_comp`, which is the case `k = f ≫ g`: after
`subst` the first factor of that statement is `AlgebraicGeometry.pullbackSpecMapCompIso`, which
`specCompFunIso_trans` cancels. Like its input it is an equality of isomorphisms, not of their
`hom`s. -/
theorem pullbackTildeIso_app_comp_of_eq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (k : R ⟶ T) (hk : f ≫ g = k) (hs : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat.{u} R) :
    (specCompFunIso f g k hs).app ((tilde.functor R).obj M) ≪≫
        (pullbackTildeIso R T k).app M =
      (Scheme.Modules.pullback (Spec.map g)).mapIso ((pullbackTildeIso R S f).app M) ≪≫
        (pullbackTildeIso S T g).app ((ModuleCat.extendScalars f.hom).obj M) ≪≫
        (tilde.functor T).mapIso ((extendScalarsCompOf f.hom g.hom k.hom
          (congrArg CommRingCat.Hom.hom hk)).app M).symm := by
  subst hk
  refine isoCancelLeft _ ((pullbackSpecMapCompIso R S T f g).app ((tilde.functor R).obj M)) ?_
    (pullbackTildeIso_app_comp R S T f g M)
  exact ((isoAppTrans _ _ ((tilde.functor R).obj M)).symm.trans
    (isoAppCongr ((tilde.functor R).obj M) (specCompFunIso_trans f g hs))).trans
    (isoAppRefl _ ((tilde.functor R).obj M))

/-! ### The chart comparison over the rings, as a morphism of modules -/

variable {X : Scheme.{u}}

/-- **The chart comparison of the determinant over the rings composes, as an identity of
morphisms of modules.** This is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_trans` with the cancellation
`TensorProduct.AlgebraTensorModule.cancelBaseChange` written as the component of
`AlgebraicGeometry.DeterminantTwoTerm.extendScalarsCompOf`, which is the shape the comparison on
the spectra reads it in.

The two spellings agree by
`AlgebraicGeometry.DeterminantTwoTerm.extendScalarsCompOf_app_hom` and
`AlgebraicGeometry.DeterminantTwoTerm.extendScalars_map_hom`. -/
theorem chartDetModuleIso_trans_hom (L : PerfectTwoTermAmplitude X) {V V' W : X.affineOpens}
    (h : V ≤ V') (h' : V' ≤ W) :
    (ModuleCat.extendScalars (affineRestriction X h).hom).map
          (chartDetModuleIso L h').toModuleIso.hom ≫
        (chartDetModuleIso L h).toModuleIso.hom =
      (extendScalarsCompOf (affineRestriction X h').hom (affineRestriction X h).hom
            (affineRestriction X (h.trans h')).hom (affineRestriction_hom_comp h h')).inv.app
          ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj ≫
        (chartDetModuleIso L (h.trans h')).toModuleIso.hom := by
  refine eq_inv_comp_of_hom_comp
    (extendScalarsCompOf (affineRestriction X h').hom (affineRestriction X h).hom
      (affineRestriction X (h.trans h')).hom (affineRestriction_hom_comp h h')) _
    (ModuleCat.hom_ext ?_)
  refine Eq.trans (hom_comp_three _ _ _) ?_
  refine Eq.trans (linComp_congr _
    (extendScalars_map_hom (affineRestriction X h).hom
      (chartDetModuleIso L h').toModuleIso.hom)
    (extendScalarsCompOf_app_hom _ _ _ (affineRestriction_hom_comp h h') _)) ?_
  exact chartDetModuleIso_trans L h h'

/-! ### The chart comparison on the spectra is transitive -/

/-- The factorisation `AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso` of the
pullback is the component of the functor-level factorisation
`AlgebraicGeometry.DeterminantTwoTerm.specCompFunIso`. This is an equality of isomorphisms, not
of their `hom`s: expanding the `hom` of either side forces the kernel to reconcile the two
spellings of the component of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, and it does not
terminate. -/
private theorem chartSpecPullbackCompIso_eq_app {V V' W : X.affineOpens} (h : V ≤ V')
    (h' : V' ≤ W) (M : (Spec Γ(X, (W.1 : X.Opens))).Modules) :
    chartSpecPullbackCompIso h h' M =
      (specCompFunIso (affineRestriction X h') (affineRestriction X h)
        (affineRestriction X (h.trans h'))
        (specMap_chartRestriction_comp (AffineOpensGlue.coe_le_coe h)
          (AffineOpensGlue.coe_le_coe h'))).app M :=
  (isoAppTrans _ _ M).symm

/-- **The associativity chase behind
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_trans`,** with every category,
functor, object and isomorphism a variable.

Read `Pg` as the pullback along `Spec ρ_{V,V'}`, `TS` and `TT` as the associated-sheaf functors
over `Γ(X, V')` and `Γ(X, V)`, `Eg` as extension of scalars along `ρ_{V,V'}`, `A`, `Bp`, `Bq` and
`C` as components of the affine pullback comparison of [Stacks, Tag 01I9], `a`, `b` and `c` as
the chart comparisons of the determinant over the rings, `γ` as the composition isomorphism of
the two extensions of scalars and `D` as the factorisation of the pullback.

The chase is: `hk`, the composition compatibility of the comparison, expands `D ≪≫ C`; `hring`,
the cocycle over the rings, matches the two tails under `TT`; and `hnat`, the naturality of the
comparison in the module, moves `Pg.map (TS.map a.hom)` past `Bq.hom`. -/
private theorem specChaseIso {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    [Category 𝒟] (Pg : ℬ ⥤ 𝒟) (TS : 𝒜 ⥤ ℬ) (TT : 𝒞 ⥤ 𝒟) (Eg : 𝒜 ⥤ 𝒞) {u₀ : ℬ} {p q : 𝒜}
    {w y : 𝒞} {z : 𝒟} (A : u₀ ≅ TS.obj p) (a : p ≅ q)
    (Bp : Pg.obj (TS.obj p) ≅ TT.obj (Eg.obj p)) (Bq : Pg.obj (TS.obj q) ≅ TT.obj (Eg.obj q))
    (b : Eg.obj q ≅ y) (γ : Eg.obj p ≅ w) (c : w ≅ y) (D : Pg.obj u₀ ≅ z) (C : z ≅ TT.obj w)
    (hnat : Pg.map (TS.map a.hom) ≫ Bq.hom = Bp.hom ≫ TT.map (Eg.map a.hom))
    (hk : D ≪≫ C = Pg.mapIso A ≪≫ Bp ≪≫ TT.mapIso γ)
    (hring : Eg.map a.hom ≫ b.hom = γ.hom ≫ c.hom) :
    Pg.map (A ≪≫ TS.mapIso a).hom ≫ (Bq ≪≫ TT.mapIso b).hom =
      D.hom ≫ (C ≪≫ TT.mapIso c).hom := by
  have hk' := congrArg Iso.hom hk
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hk'
  simp only [Iso.trans_hom, Functor.mapIso_hom, Pg.map_comp, Category.assoc]
  rw [← Category.assoc D.hom, hk']
  simp only [Category.assoc]
  rw [← TT.map_comp, ← hring, TT.map_comp, ← reassoc_of% hnat]

/-- **The chart comparison of the determinant on the spectra composes.** Let `X` be a scheme,
`L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and `V ≤ V' ≤ W` affine opens of
`X`. Pulling the comparison for `V' ≤ W` back along `Spec ρ_{V,V'}` and following it with the
comparison for `V ≤ V'` is the comparison for `V ≤ W`, read through the factorisation
`AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso` of the pullback.

The comparison on the spectra is the affine pullback comparison of [Stacks, Tag 01I9] followed
by the associated sheaf of the comparison over the rings, so the identity is the composition
compatibility
`AlgebraicGeometry.DeterminantTwoTerm.pullbackTildeIso_app_comp_of_eq` of the first, its
naturality in the module, and the cocycle
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_trans_hom` of the second, put together
by `AlgebraicGeometry.DeterminantTwoTerm.specChaseIso`. -/
theorem chartDetSpecPullbackIso_trans (L : PerfectTwoTermAmplitude X)
    {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W) :
    (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecPullbackIso L h').hom ≫
        (chartDetSpecPullbackIso L h).hom =
      (chartSpecPullbackCompIso h h' (chartDetSpec L W)).hom ≫
        (chartDetSpecPullbackIso L (h.trans h')).hom := by
  refine specChaseIso (Scheme.Modules.pullback (Spec.map (affineRestriction X h)))
    (tilde.functor Γ(X, (V'.1 : X.Opens))) (tilde.functor Γ(X, (V.1 : X.Opens)))
    (ModuleCat.extendScalars (affineRestriction X h).hom)
    ((pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V'.1 : X.Opens))
      (affineRestriction X h')).app
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj)
    (chartDetModuleIso L h').toModuleIso
    ((pullbackTildeIso Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
      (affineRestriction X h)).app
        ((ModuleCat.extendScalars (affineRestriction X h').hom).obj
          ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj))
    ((pullbackTildeIso Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
      (affineRestriction X h)).app
        ((det Γ(X, (V'.1 : X.Opens))).obj ⟨chartComplex L V'⟩).of.obj)
    (chartDetModuleIso L h).toModuleIso
    ((extendScalarsCompOf (affineRestriction X h').hom (affineRestriction X h).hom
      (affineRestriction X (h.trans h')).hom (affineRestriction_hom_comp h h')).app
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj).symm
    (chartDetModuleIso L (h.trans h')).toModuleIso
    (chartSpecPullbackCompIso h h' (chartDetSpec L W))
    ((pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
      (affineRestriction X (h.trans h'))).app
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj)
    ?_ ?_ ?_
  · exact natComp (Scheme.Modules.pullback (Spec.map (affineRestriction X h)))
      (tilde.functor Γ(X, (V'.1 : X.Opens))) (tilde.functor Γ(X, (V.1 : X.Opens)))
      (ModuleCat.extendScalars (affineRestriction X h).hom)
      (pullbackTildeIso Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
        (affineRestriction X h)).hom
      ((ModuleCat.extendScalars (affineRestriction X h').hom).obj
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj)
      ((det Γ(X, (V'.1 : X.Opens))).obj ⟨chartComplex L V'⟩).of.obj
      (chartDetModuleIso L h').toModuleIso.hom
  · exact (transCongrLeft _ (chartSpecPullbackCompIso_eq_app h h' (chartDetSpec L W))).trans
      (pullbackTildeIso_app_comp_of_eq (affineRestriction X h') (affineRestriction X h)
        (affineRestriction X (h.trans h'))
        (chartRestriction_comp (AffineOpensGlue.coe_le_coe h) (AffineOpensGlue.coe_le_coe h'))
        (specMap_chartRestriction_comp (AffineOpensGlue.coe_le_coe h)
          (AffineOpensGlue.coe_le_coe h'))
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj)
  · exact chartDetModuleIso_trans_hom L h h'

end AlgebraicGeometry.DeterminantTwoTerm

end

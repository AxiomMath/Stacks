module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.FiniteLocallyFree

/-!
# The canonical section of `p^*ℰ` on the vector bundle of `𝒩`

Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules and
`p : N = Spec_X(Sym(𝒩^∨)) ⟶ X` the vector bundle of `𝒩`. The surjection `𝒩 ⟶ ℰ` gives
`ℰ^∨ ⟶ 𝒩^∨ ⟶ Sym(𝒩^∨) = p_* 𝒪_N`, and by adjunction a cosection `p^*(ℰ^∨) ⟶ 𝒪_N`, that is a
global section of `(p^*(ℰ^∨))^∨ ≅ p^*ℰ`. This is the canonical section of [Stacks, Tag 0FAA],
the element of `Γ(N, p^*ℰ) ⊇ Γ(X, Hom(𝒩, ℰ))` corresponding to `𝒩 ⟶ ℰ`. Its zero scheme is
`N' = Spec_X(Sym((𝒩')^∨)) ⊆ N`.

## Main definitions

* `Stacks.Chow.subbundleCosection` — the cosection `p^*(ℰ^∨) ⟶ 𝒪_N`.
* `Stacks.Chow.subbundleSection` — the corresponding global section of `(p^*(ℰ^∨))^∨`.

## Main results

* `Stacks.Chow.pullbackGlobalSections_subbundleSection_eq_zero_iff` — a pullback of the section
  vanishes exactly when the functions `φ(m)` attached to the sections `m` of `ℰ^∨` do.
* `Stacks.Chow.zeroScheme_subbundleSection` — **the zero scheme of the canonical section is
  `N'`**.

## Implementation notes

The morphisms of algebra sheaves out of `Sym(ℱ)` are written in the category
`Stacks.RelativeSpec.AlgebraSheaf X` of the relative spectrum, while the universal property of
`Sym` (`Stacks.SymAlgSheaf.algebraLift`) is stated in the category of quasi-coherent algebras and
for the module spelled as a sheaf of modules over `X.ringCatSheaf`. The declarations of the first
section restate that universal property at the spelling `X.Modules` and in the category of algebra
sheaves, so that rewriting with it does not have to cross between the two category instances.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0FA8](https://stacks.math.columbia.edu/tag/0FA8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-! ### The universal property of `Sym`, at the spelling `X.Modules` -/

/-- The degree-one generator `ℱ ⟶ Sym(ℱ)`, as a morphism of `𝒪_X`-modules into the module
underlying the algebra sheaf `Sym(ℱ)`. -/
def symGen (F : X.Modules) :
    F ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
      (Scheme.Modules.symmetricAlgebraSheaf X F) :=
  Stacks.SymAlgSheaf.symmetricAlgebraSheafι F

/-- The generator of `Sym` is natural: `ι_ℱ ≫ Sym(f) = f ≫ ι_𝒢`. -/
theorem symGen_comp_symmetricAlgebraSheafMap {F G : X.Modules} (f : F ⟶ G) :
    symGen F ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (Scheme.Modules.symmetricAlgebraSheafMap X f) = f ≫ symGen G := by
  have h1 : Stacks.SymAlgSheaf.algebraLift (Scheme.Modules.symmetricAlgebraSheaf X G) G
      (Stacks.SymAlgSheaf.symmetricAlgebraSheafι G) = 𝟙 _ :=
    (Stacks.SymAlgSheaf.eq_algebraLift _ G (𝟙 _)).symm
  have h2 : Scheme.Modules.symmetricAlgebraSheafMap X f =
      Stacks.SymAlgSheaf.algebraLift (Scheme.Modules.symmetricAlgebraSheaf X G) F
        (f ≫ Stacks.SymAlgSheaf.symmetricAlgebraSheafι G) :=
    ((Category.comp_id _).symm.trans (congrArg (fun t => _ ≫ t) h1.symm)).trans
      (Stacks.SymAlgSheaf.algebraLift_comp _ f _).symm
  rw [h2]
  exact Stacks.SymAlgSheaf.symmetricAlgebraSheafι_comp_algebraLift _ F _

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The morphism of algebra sheaves `Sym(ℱ) ⟶ 𝒜` lifting a morphism of modules `ℱ ⟶ 𝒜`. -/
def symLift (𝒜 : Stacks.RelativeSpec.AlgebraSheaf X) (F : X.Modules)
    (β : F ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule 𝒜) :
    Scheme.Modules.symmetricAlgebraSheaf X F ⟶ 𝒜 :=
  Stacks.SymAlgSheaf.algebraLift 𝒜 F β

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- **Uniqueness in the universal property of `Sym`**: a morphism of algebra sheaves out of
`Sym(ℱ)` is the lift of its restriction to the generator. -/
theorem eq_symLift {𝒜 : Stacks.RelativeSpec.AlgebraSheaf X} {F : X.Modules}
    (Ψ : Scheme.Modules.symmetricAlgebraSheaf X F ⟶ 𝒜) :
    Ψ = symLift 𝒜 F (symGen F ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap Ψ) :=
  Stacks.SymAlgSheaf.eq_algebraLift 𝒜 F Ψ

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The lift is compatible with `Sym(f)`. -/
theorem symmetricAlgebraSheafMap_comp_symLift {𝒜 : Stacks.RelativeSpec.AlgebraSheaf X}
    {F G : X.Modules} (f : F ⟶ G)
    (β : G ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule 𝒜) :
    Scheme.Modules.symmetricAlgebraSheafMap X f ≫ symLift 𝒜 G β = symLift 𝒜 F (f ≫ β) :=
  (Stacks.SymAlgSheaf.algebraLift_comp 𝒜 f β).symm

/-- The algebra `p_* 𝒪_N` of the vector bundle `N = 𝐕(𝒩^∨)`. -/
abbrev bundleAlgebra (N : X.Modules) [N.IsQuasicoherent] : Stacks.RelativeSpec.AlgebraSheaf X :=
  pushforwardAlgebra (Scheme.Modules.vectorBundleOver X (F := N)).hom

/-- **[Stacks, Tag 01LX] (3)** for `N = 𝐕(ℱ)`: `p_* 𝒪_N ≅ Sym(ℱ)`. -/
def bundleAlgebraIso (F : X.Modules) [F.IsQuasicoherent] :
    bundleAlgebra F ≅ Scheme.Modules.symmetricAlgebraSheaf X F :=
  Scheme.Modules.vectorBundlePushforwardIso X

/-- The morphism of vector bundles over `X` induced by a morphism of quasi-coherent modules. -/
def bundleMapOver {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    Scheme.Modules.vectorBundleOver X (F := G) ⟶ Scheme.Modules.vectorBundleOver X (F := F) :=
  Scheme.Modules.vectorBundleMap X f

/-- Under `bundleAlgebraIso`, the morphism of algebras `p_* 𝒪` induced by `bundleMapOver f` is
`Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)`. -/
theorem pushforwardAlgebraMap_bundleMapOver {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (f : F ⟶ G) :
    pushforwardAlgebraMap (bundleMapOver f) =
      (bundleAlgebraIso F).hom ≫ Scheme.Modules.symmetricAlgebraSheafMap X f ≫
        (bundleAlgebraIso G).inv :=
  Scheme.Modules.pushforwardAlgebraMap_vectorBundleMap X f

/-- The morphism of vector bundles induced by the dual `𝒩^∨ ⟶ (𝒩')^∨` of `inc : 𝒩' ⟶ 𝒩` is
`subbundleEmbedding N' N inc`. -/
theorem bundleMapOver_left (inc : N' ⟶ N) :
    (bundleMapOver (dualMap inc)).left = subbundleEmbedding N' N inc := rfl

/-! ### The canonical cosection -/

/-- The module `p^*(ℰ^∨)` on the vector bundle `N` of `𝒩`. -/
abbrev subbundleDualPullback : (dualVectorBundle N).Modules :=
  (Scheme.Modules.pullback (dualVectorBundleToBase N)).obj (dualSheaf E)

/-- The morphism `ℰ^∨ ⟶ 𝒩^∨ ⟶ Sym(𝒩^∨) = p_* 𝒪_N`. -/
def subbundleCosectionAdj (pr : N ⟶ E) :
    dualSheaf E ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule (bundleAlgebra (dualSheaf N)) :=
  dualMap pr ≫ symGen (dualSheaf N) ≫
    Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap (bundleAlgebraIso (dualSheaf N)).inv

/-- **The canonical cosection** `p^*(ℰ^∨) ⟶ 𝒪_N`. -/
def subbundleCosection (pr : N ⟶ E) :
    subbundleDualPullback N E ⟶ SheafOfModules.unit (dualVectorBundle N).ringCatSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).homEquiv _ _).symm
    (subbundleCosectionAdj N E pr : dualSheaf E ⟶ (Scheme.Modules.pushforward
      (dualVectorBundleToBase N)).obj (SheafOfModules.unit (dualVectorBundle N).ringCatSheaf))

/-- **The canonical section** of `(p^*(ℰ^∨))^∨`. -/
def subbundleSection (pr : N ⟶ E) : Γ(dualSheaf (subbundleDualPullback N E), ⊤) :=
  Stacks.FundamentalGroup.dualSectionsHom _ (subbundleCosection N E pr)

/-- Restricting the canonical cosection adjoint along `g` is `ℰ^∨ ⟶ Sym(𝒩^∨)` followed by the
algebra map `Sym(𝒩^∨) ⟶ p_* 𝒪` induced by `g`. -/
private theorem subbundleCosectionAdj_comp_pushforwardAlgebraMap {M F : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] {Y : Over X} (pr : M ⟶ F)
    (g : Y ⟶ Scheme.Modules.vectorBundleOver X (F := dualSheaf M)) :
    subbundleCosectionAdj M F pr ≫
        Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap g) =
      dualMap pr ≫ symGen (dualSheaf M) ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        ((bundleAlgebraIso (dualSheaf M)).inv ≫ pushforwardAlgebraMap g) := by
  rw [subbundleCosectionAdj, ← Stacks.FundamentalGroup.underlyingModuleMap_comp', Category.assoc,
    Category.assoc]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- **The canonical cosection vanishes on `N'`**, in adjoint form: `ℰ^∨ ⟶ Sym(𝒩^∨) ⟶ p'_* 𝒪_{N'}`
is zero. -/
theorem subbundleCosectionAdj_comp_bundleMapOver (inc : N' ⟶ N) (pr : N ⟶ E)
    (w : dualMap pr ≫ dualMap inc = 0) :
    subbundleCosectionAdj N E pr ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMap (bundleMapOver (dualMap inc))) = 0 := by
  have h' : (bundleAlgebraIso (dualSheaf N)).inv ≫
      pushforwardAlgebraMap (bundleMapOver (dualMap inc)) =
      Scheme.Modules.symmetricAlgebraSheafMap X (dualMap inc) ≫
        (bundleAlgebraIso (dualSheaf N')).inv := by
    rw [pushforwardAlgebraMap_bundleMapOver, Iso.inv_hom_id_assoc]
  rw [subbundleCosectionAdj_comp_pushforwardAlgebraMap, h',
    ← Stacks.FundamentalGroup.underlyingModuleMap_comp', ← Category.assoc (symGen _),
    symGen_comp_symmetricAlgebraSheafMap, Category.assoc, ← Category.assoc (dualMap pr), w,
    zero_comp]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The canonical cosection on the canonical image of a section of `ℰ^∨`. -/
theorem subbundleCosection_unit (pr : N ⟶ E) (W : X.Opens) (m : (dualSheaf E).val.obj (op W)) :
    (subbundleCosection N E pr).val.app (op (dualVectorBundleToBase N ⁻¹ᵁ W))
        (((Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).unit.app
          (dualSheaf E)).val.app (op W) m) =
      (subbundleCosectionAdj N E pr).val.app (op W) m := by
  have h := Adjunction.homEquiv_unit
    (Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)) (dualSheaf E)
    (SheafOfModules.unit (dualVectorBundle N).ringCatSheaf) (subbundleCosection N E pr)
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).homEquiv _ _
      (subbundleCosection N E pr) = subbundleCosectionAdj N E pr :=
    Equiv.apply_symm_apply _ _
  exact (congrArg (fun t => t.val.app (op W) m) (h2.symm.trans h)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The adjoint of a morphism out of `p^*(ℰ^∨)` on a section of `ℰ^∨`. -/
theorem homEquiv_val_app_unit {M : (dualVectorBundle N).Modules}
    (f : subbundleDualPullback N E ⟶ M) (W : X.Opens) (m : (dualSheaf E).val.obj (op W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).homEquiv _ _
        f).val.app (op W) m =
      f.val.app (op (dualVectorBundleToBase N ⁻¹ᵁ W))
        (((Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).unit.app
          (dualSheaf E)).val.app (op W) m) := by
  rw [Adjunction.homEquiv_unit]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- A morphism of `𝒪_X`-modules equal to zero vanishes on every section. -/
theorem modules_app_apply_eq_zero {M M' : X.Modules} {t : M ⟶ M'} (ht : t = 0) (U : X.Opens)
    (m : Γ(M, U)) : Scheme.Modules.Hom.app t U m = 0 := by
  subst ht
  rw [Scheme.Modules.Hom.zero_app]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- A composite of morphisms of `𝒪_X`-modules equal to zero kills every section. -/
theorem modules_comp_app_apply_eq_zero {M M' M'' : X.Modules} (f : M ⟶ M') (g : M' ⟶ M'')
    (h : f ≫ g = 0) (U : X.Opens) (m : Γ(M, U)) :
    Scheme.Modules.Hom.app g U (Scheme.Modules.Hom.app f U m) = 0 :=
  modules_app_apply_eq_zero h U m

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- On sections, the morphism of underlying modules of a morphism of algebra sheaves is that
morphism. -/
theorem underlyingModuleMap_app_apply {A B : Stacks.RelativeSpec.AlgebraSheaf X} (f : A ⟶ B)
    (W : X.Opens) (y : A.right.obj.obj (op W)) :
    Scheme.Modules.Hom.app (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap f) W y =
      (f.right.hom.app (op W)).hom y := rfl

section ZeroLocus

variable (e : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]

/-- If `ℰ` is finite locally free of rank `e`, then so is `p^*(ℰ^∨)`. -/
instance isFiniteLocallyFreeOfRank_subbundleDualPullback :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (subbundleDualPullback N E) e :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ e

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include e in
/-- **The pullback of the canonical section vanishes exactly where the canonical cosection
does.** For `g : T ⟶ N`, `g^* s = 0` if and only if every function `φ(m) ∈ Γ(N, p⁻¹ W)` attached
to a section `m` of `ℰ^∨` pulls back to zero on `T`. -/
theorem pullbackGlobalSections_subbundleSection_eq_zero_iff (pr : N ⟶ E) {T : Scheme.{u}}
    (g : T ⟶ dualVectorBundle N) :
    pullbackGlobalSections g _ (subbundleSection N E pr) = 0 ↔
      ∀ (W : X.Opens) (m : (dualSheaf E).val.obj (op W)),
        (g.app (dualVectorBundleToBase N ⁻¹ᵁ W)).hom
          ((subbundleCosectionAdj N E pr).val.app (op W) m) = 0 := by
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (subbundleDualPullback N E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ e
  let D := Stacks.FundamentalGroup.dualNeighborhoodEquiv g (subbundleDualPullback N E) hM
  let H := (Scheme.Modules.pullbackPushforwardAdjunction (dualVectorBundleToBase N)).homEquiv
    (dualSheaf E) ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
  have hs : ∀ (W : X.Opens) (m : (dualSheaf E).val.obj (op W)),
      (H (D (pullbackGlobalSections g _ (subbundleSection N E pr)))).val.app (op W) m =
        (g.app (dualVectorBundleToBase N ⁻¹ᵁ W)).hom
          ((subbundleCosectionAdj N E pr).val.app (op W) m) := by
    intro W m
    refine (homEquiv_val_app_unit N E _ W m).trans ?_
    refine (Stacks.FundamentalGroup.dualNeighborhoodEquiv_pullbackGlobalSections_val_app g _ hM
      (subbundleCosection N E pr) _ _).trans ?_
    rw [subbundleCosection_unit]
  have h0 : ∀ (W : X.Opens) (m : (dualSheaf E).val.obj (op W)),
      (H (D 0)).val.app (op W) m = 0 := by
    intro W m
    refine (homEquiv_val_app_unit N E _ W m).trans ?_
    refine (Stacks.FundamentalGroup.dualNeighborhoodEquiv_val_app g _ hM 0 _ _).trans ?_
    rw [map_zero]
    rfl
  constructor
  · intro h W m
    refine (hs W m).symm.trans ?_
    rw [h]
    exact h0 W m
  · intro h
    refine D.injective (H.injective ?_)
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
      (LinearMap.ext fun m => ?_))
    exact (hs W.unop m).trans ((h W.unop m).trans (h0 W.unop m).symm)

/-- A section killed by `appLE` along an equality of opens is killed by `app`. -/
theorem app_apply_eq_zero_of_appLE {A B : Scheme.{u}} (f : A ⟶ B) {U : B.Opens} {V : A.Opens}
    (h : f ⁻¹ᵁ U = V) (x : Γ(B, U)) (hx : (f.appLE U V h.ge).hom x = 0) :
    (f.app U).hom x = 0 := by
  subst h
  rwa [Scheme.Hom.appLE_eq_app] at hx

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include e in
/-- **The canonical section vanishes on `N'`**: its zero scheme is contained in `N'`. -/
theorem zeroScheme_subbundleSection_le (inc : N' ⟶ N) (pr : N ⟶ E)
    (w : dualMap pr ≫ dualMap inc = 0) :
    Stacks.RegularSectionSequence.zeroScheme (dualVectorBundle N)
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr) ≤
      (subbundleEmbedding N' N inc).ker := by
  have hi : pullbackGlobalSections (subbundleEmbedding N' N inc) _ (subbundleSection N E pr) =
      0 := by
    refine (pullbackGlobalSections_subbundleSection_eq_zero_iff N E e pr _).mpr fun W m => ?_
    have h1 := modules_comp_app_apply_eq_zero _ _
      (subbundleCosectionAdj_comp_bundleMapOver N' N E inc pr w) W m
    have h2 := (underlyingModuleMap_app_apply _ W _).symm.trans h1
    rw [pushforwardAlgebraMap_app _ W (preimage_le_preimage_preimage _ W)] at h2
    rw [← bundleMapOver_left N' N inc]
    have hW : (bundleMapOver (dualMap inc)).left ⁻¹ᵁ
        ((Scheme.Modules.vectorBundleOver X (F := dualSheaf N)).hom ⁻¹ᵁ W) =
        (Scheme.Modules.vectorBundleOver X (F := dualSheaf N')).hom ⁻¹ᵁ W :=
      congrArg (fun q => q ⁻¹ᵁ W) (Over.w (bundleMapOver (dualMap inc)))
    exact app_apply_eq_zero_of_appLE (bundleMapOver (dualMap inc)).left hW _ h2
  obtain ⟨k, hk⟩ :=
    (Stacks.RegularSectionSequence.pullbackGlobalSections_eq_zero_iff_factorsThrough_zeroScheme
      _ e _ _).mp hi
  rw [← hk]
  refine le_trans (le_of_eq ?_) (Scheme.Hom.le_ker_comp k _)
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- A morphism of `𝒪_X`-modules killing every section is zero. -/
theorem modules_comp_eq_zero_of_app {M M' M'' : X.Modules} (f : M ⟶ M') (g : M' ⟶ M'')
    (h : ∀ (U : X.Opens) (m : Γ(M, U)),
      Scheme.Modules.Hom.app g U (Scheme.Modules.Hom.app f U m) = 0) : f ≫ g = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h U m,
    Scheme.Modules.Hom.zero_app]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- A section killed by `app` is killed by `appLE` along an equality of opens. -/
theorem appLE_apply_eq_zero_of_app {A B : Scheme.{u}} (f : A ⟶ B) {U : B.Opens} {V : A.Opens}
    (h : f ⁻¹ᵁ U = V) (x : Γ(B, U)) (hx : (f.app U).hom x = 0) :
    (f.appLE U V h.ge).hom x = 0 := by
  subst h
  rwa [Scheme.Hom.appLE_eq_app]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include e in
/-- **`N'` lies in the zero scheme of the canonical section.** -/
theorem ker_subbundleEmbedding_le_zeroScheme (inc : N' ⟶ N) (pr : N ⟶ E)
    (w : dualMap pr ≫ dualMap inc = 0)
    (hS : (ShortComplex.mk (dualMap pr) (dualMap inc) w).ShortExact) :
    (subbundleEmbedding N' N inc).ker ≤
      Stacks.RegularSectionSequence.zeroScheme (dualVectorBundle N)
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr) := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := dualSheaf N)
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := dualSheaf N')
  have := hS.epi_g
  set Z := Stacks.RegularSectionSequence.zeroScheme (dualVectorBundle N)
    (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr) with hZdef
  have hZ0 : pullbackGlobalSections Z.subschemeι _ (subbundleSection N E pr) = 0 :=
    Stacks.RegularSectionSequence.pullbackGlobalSections_subschemeι_eq_zero _ e _
  have hcrit := (pullbackGlobalSections_subbundleSection_eq_zero_iff N E e pr _).mp hZ0
  let Zo : Over X := Over.mk (Z.subschemeι ≫ (Scheme.Modules.vectorBundleOver X
    (F := dualSheaf N)).hom)
  let g' : Zo ⟶ Scheme.Modules.vectorBundleOver X (F := dualSheaf N) :=
    Over.homMk Z.subschemeι rfl
  let α : Scheme.Modules.symmetricAlgebraSheaf X (dualSheaf N) ⟶ pushforwardAlgebra Zo.hom :=
    (bundleAlgebraIso (dualSheaf N)).inv ≫ pushforwardAlgebraMap g'
  have hα0 : dualMap pr ≫ symGen (dualSheaf N) ≫
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap α = 0 := by
    rw [← subbundleCosectionAdj_comp_pushforwardAlgebraMap]
    refine modules_comp_eq_zero_of_app _ _ fun U m => ?_
    refine (underlyingModuleMap_app_apply _ U _).trans ?_
    rw [pushforwardAlgebraMap_app _ U (preimage_le_preimage_preimage _ U)]
    exact appLE_apply_eq_zero_of_app Z.subschemeι rfl _ (hcrit U m)
  let β : dualSheaf N' ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
      (pushforwardAlgebra Zo.hom) :=
    hS.exact.desc (symGen (dualSheaf N) ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap α)
      hα0
  have hβ : dualMap inc ≫ β =
      symGen (dualSheaf N) ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap α :=
    hS.exact.g_desc _ hα0
  let α' := symLift (pushforwardAlgebra Zo.hom) (dualSheaf N') β
  have key : Scheme.Modules.symmetricAlgebraSheafMap X (dualMap inc) ≫ α' = α := by
    rw [symmetricAlgebraSheafMap_comp_symLift, hβ]
    exact (eq_symLift α).symm
  let h'' : Zo ⟶ Scheme.Modules.vectorBundleOver X (F := dualSheaf N') :=
    (overHomEquivAlgebraHom Zo (Scheme.Modules.vectorBundleOver X (F := dualSheaf N'))).symm
      ((bundleAlgebraIso (dualSheaf N')).hom ≫ α')
  have hh'' : pushforwardAlgebraMap h'' = (bundleAlgebraIso (dualSheaf N')).hom ≫ α' := by
    rw [← overHomEquivAlgebraHom_apply, Equiv.apply_symm_apply]
  have hcomp : h'' ≫ bundleMapOver (dualMap inc) = g' := by
    apply (overHomEquivAlgebraHom Zo (Scheme.Modules.vectorBundleOver X
      (F := dualSheaf N))).injective
    rw [overHomEquivAlgebraHom_apply, overHomEquivAlgebraHom_apply, pushforwardAlgebraMap_comp,
      pushforwardAlgebraMap_bundleMapOver, hh'', Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc, key, Iso.hom_inv_id_assoc]
  have hleft : h''.left ≫ subbundleEmbedding N' N inc = Z.subschemeι :=
    congrArg (fun t => t.left) hcomp
  calc (subbundleEmbedding N' N inc).ker ≤ (h''.left ≫ subbundleEmbedding N' N inc).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = Z.subschemeι.ker := by rw [hleft]
    _ = Z := Scheme.IdealSheafData.ker_subschemeι _

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include e in
/-- **The zero scheme of the canonical section is `N'`.** -/
theorem zeroScheme_subbundleSection (inc : N' ⟶ N) (pr : N ⟶ E)
    (w : dualMap pr ≫ dualMap inc = 0)
    (hS : (ShortComplex.mk (dualMap pr) (dualMap inc) w).ShortExact) :
    Stacks.RegularSectionSequence.zeroScheme (dualVectorBundle N)
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr) =
      (subbundleEmbedding N' N inc).ker :=
  le_antisymm (zeroScheme_subbundleSection_le N' N E e inc pr w)
    (ker_subbundleEmbedding_le_zeroScheme N' N E e inc pr w hS)

end ZeroLocus

end Stacks.Chow

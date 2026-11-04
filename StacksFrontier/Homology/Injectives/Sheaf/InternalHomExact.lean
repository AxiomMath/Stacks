module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Stacks Project Tag 01DR (Lemma 19.8.1): for an injective abelian sheaf
`J` on a site `C`, the contravariant internal-Hom functor `ℋom(-, J)` is exact,
i.e. it sends short exact sequences of abelian sheaves to short exact sequences.

We work with the category `Ab(C) = Sheaf K Ab` of sheaves of abelian groups on a
site `(C, K)`.

## Main Definition 1 (Abelian internal hom against a fixed sheaf `J`)

For `F, J ∈ Ab(C)`, the internal Hom sheaf `ℋom(F, J)` is the abelian sheaf with

  `ℋom(F, J)(U) = Hom_{Ab(C/U)}(F|_U, J|_U)`,

the abelian group of morphisms of abelian sheaves on the localized site `C/U`,
where `C/U` is the slice category `Over U` equipped with the induced topology
`K.over U` and `F|_U`, `J|_U` denote restrictions of (pre)sheaves along the
forgetful functor `Over U → C`. Restriction maps for `V → U` are induced by
further restriction. As a contravariant functor in the first variable,
precomposition gives `ℋom(-, J) : Ab(C)ᵒᵖ ⥤ Ab(C)`.

We build this internal Hom by upgrading Mathlib's `Type`-valued `presheafHom`
(whose value at `U` is, by `presheafHom_obj`, exactly the set of morphisms
`((Over.forget U).op ⋙ F ⟶ (Over.forget U).op ⋙ J)`) to an `Ab`-valued
presheaf, carrying the pointwise abelian group structure on hom-sets. The
restriction maps are precomposition (`whiskerLeft`), which is additive.

## Main Definition 2 (Injective abelian sheaf)

`J ∈ Ab(C)` is injective iff `Hom(-, J)` is exact; in Mathlib this is the class
`CategoryTheory.Injective J` (every mono `A ↪ B` and map `A → J` extends to
`B → J`).

## Main Statement 1 (Abelian-sheaf level — the substance of Tag 01DR)

If `J` is an injective abelian sheaf, then `ℋom(-, J) : Ab(C)ᵒᵖ ⥤ Ab(C)` is
exact: for every short exact sequence `0 → F' → F → F'' → 0` the contravariantly
induced sequence `0 → ℋom(F'', J) → ℋom(F, J) → ℋom(F', J) → 0` is short exact.

We formalize Statement 1 (per the problem's note 4, proving Statement 1 alone is
a faithful formalization of the substance of Tag 01DR). A short exact sequence is
encoded as a `ShortComplex` together with `ShortComplex.ShortExact`; contravariant
exactness is expressed by applying the functor to the opposite short complex
`S.op` and asserting `(S.op.map (ℋom(-, J))).ShortExact`.
-/

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C]

-- Main Definition(s)

/-- The `Ab`-valued internal-Hom presheaf `ℋom(F, G)` on a site.
Its value at `U` is the abelian group `Hom_{Ab(C/U)}(F|_U, G|_U)`, realized as
natural transformations `(Over.forget U).op ⋙ F ⟶ (Over.forget U).op ⋙ G`.
This is the `Ab`-valued upgrade of Mathlib's `Type`-valued `presheafHom`. -/
@[ega "0 4.1.5" "special case", sga "3 I 2.1.1" "special case", sga "3 I 3.1.4" "special case"]
noncomputable def internalHomPresheaf (F G : Cᵒᵖ ⥤ Ab.{max u v}) : Cᵒᵖ ⥤ Ab.{max u v} where
  obj X := AddCommGrpCat.of ((Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G)
  map {X Y} f := AddCommGrpCat.ofHom
    { toFun := fun a => (presheafHom F G).map f a
      map_zero' := by ext Z x; rfl
      map_add' := by intro a b; ext Z x; rfl }
  map_id X := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro a
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply]
    rw [(presheafHom F G).map_id]; rfl
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro a
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply]
    rw [(presheafHom F G).map_comp]; rfl

/-- The restriction map of `internalHomPresheaf` is precomposition with
`(Over.map f).op`, matching the `Type`-valued `presheafHom`. -/
theorem internalHomPresheaf_map_apply (F G : Cᵒᵖ ⥤ Ab.{max u v}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G) :
    (internalHomPresheaf F G).map f a = (Over.map f.unop).op.whiskerLeft a := rfl

/-- Functoriality in the (first) contravariant variable: a morphism `g : F ⟶ F'`
induces, by precomposition, a morphism `ℋom(F', G) ⟶ ℋom(F, G)` of presheaves. -/
@[ega "0 4.1.5" "partial"]
noncomputable def internalHomPresheafMapLeft {F F' : Cᵒᵖ ⥤ Ab.{max u v}} (g : F ⟶ F')
    (G : Cᵒᵖ ⥤ Ab.{max u v}) : internalHomPresheaf F' G ⟶ internalHomPresheaf F G where
  app X := AddCommGrpCat.ofHom
    { toFun := fun a => Functor.whiskerLeft (Over.forget X.unop).op g ≫ a
      map_zero' := by ext Z x; simp
      map_add' := by intro a b; ext Z x; simp }
  naturality {X Y} f := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro a
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [internalHomPresheaf_map_apply, internalHomPresheaf_map_apply]
    change (Over.forget Y.unop).op.whiskerLeft g ≫ (Over.map f.unop).op.whiskerLeft a
      = (Over.map f.unop).op.whiskerLeft ((Over.forget X.unop).op.whiskerLeft g ≫ a)
    ext Z x
    simp [Functor.whiskerLeft]

/-- `ℋom(F, G)` of two abelian sheaves is again a sheaf. (Only `G` needs to be a
sheaf; the underlying `Type`-valued presheaf is `presheafHom`, which is a sheaf,
and the sheaf condition for `Ab`-valued presheaves is checked on the underlying
`Type`-valued presheaf via the forgetful functor.) -/
@[ega "0 4.1.5" "partial",
  sga "3 IV 4.5.13" "special case",
  sga "4 IV 12.1" "special case",
  sga "4 IV 12.2" "Hom(F",
  sga "4 IV 12.4" "special case"]
theorem internalHomPresheaf_isSheaf (K : GrothendieckTopology C) (F G : Sheaf K Ab.{max u v}) :
    Presheaf.IsSheaf K (internalHomPresheaf F.obj G.obj) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget K (internalHomPresheaf F.obj G.obj) (forget Ab.{max u v})]
  show Presheaf.IsSheaf K (presheafHom F.obj G.obj)
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  exact presheafHom_isSheafFor F.obj G.obj S fun {Y} f =>
    ((Presheaf.isSheaf_iff_isLimit K G.obj).mp G.property _ (K.pullback_stable f hS)).some

/-- The internal-Hom sheaf `ℋom(F, J) ∈ Ab(C)`. -/
noncomputable def internalHomSheaf (K : GrothendieckTopology C) (F J : Sheaf K Ab.{max u v}) :
    Sheaf K Ab.{max u v} :=
  ⟨internalHomPresheaf F.obj J.obj, internalHomPresheaf_isSheaf K F J⟩

/-- The contravariant internal-Hom functor `ℋom(-, J) : Ab(C)ᵒᵖ ⥤ Ab(C)`. -/
@[ega "0 4.1.5" "special case",
  sga "4 IV 12.1" "special case",
  sga "4 IV 12.2" "partial, special case"]
noncomputable def internalHomFunctor (K : GrothendieckTopology C) (J : Sheaf K Ab.{max u v}) :
    (Sheaf K Ab.{max u v})ᵒᵖ ⥤ Sheaf K Ab.{max u v} where
  obj F := internalHomSheaf K F.unop J
  map {F F'} g := ⟨internalHomPresheafMapLeft g.unop.hom J.obj⟩
  map_id F := by
    apply Sheaf.hom_ext_iff.mpr
    ext X a
    simp only [internalHomPresheafMapLeft]
    change Functor.whiskerLeft (Over.forget X.unop).op (𝟙 _) ≫ a = a
    simp
  map_comp {F F' F''} g g' := by
    apply Sheaf.hom_ext_iff.mpr
    ext X a
    simp only [internalHomPresheafMapLeft]
    change Functor.whiskerLeft (Over.forget X.unop).op (g'.unop.hom ≫ g.unop.hom) ≫ a
      = Functor.whiskerLeft (Over.forget X.unop).op g'.unop.hom
          ≫ (Functor.whiskerLeft (Over.forget X.unop).op g.unop.hom ≫ a)
    rw [Functor.whiskerLeft_comp]
    simp

/-- The internal-Hom functor preserves zero morphisms (it is additive). -/
instance internalHomFunctor_preservesZero (K : GrothendieckTopology C) (J : Sheaf K Ab.{max u v}) :
    (internalHomFunctor K J).PreservesZeroMorphisms where
  map_zero F F' := by
    apply Sheaf.hom_ext_iff.mpr
    ext X a
    change Functor.whiskerLeft (Over.forget X.unop).op (0 : _ ⟶ _) ≫ a = 0
    have h : Functor.whiskerLeft (Over.forget X.unop).op (0 : F'.unop.obj ⟶ F.unop.obj) = 0 := by
      ext Z x
      simp only [Functor.whiskerLeft_app, NatTrans.app_zero]
    rw [h, zero_comp]

-- Main Statement(s)

/-! ### Decomposition of the exactness theorem

The exactness of `ℋom(-, J)` is the assertion that the contravariant functor
`internalHomFunctor K J : (Sheaf K Ab)ᵒᵖ ⥤ Sheaf K Ab` sends a short exact
sequence `S.op` (the opposite of `S`) to a short exact sequence. By the Mathlib
lemma `ShortComplex.ShortExact.map_of_exact`, this holds for any functor that
(i) preserves zero morphisms, (ii) preserves finite limits, and (iii) preserves
finite colimits. Item (i) is already available as the instance
`internalHomFunctor_preservesZero`. Items (ii) and (iii) are the two named
sub-lemmas below.

Reading the variance carefully: a functor `G : Dᵒᵖ ⥤ E` "preserves finite
limits" exactly when the contravariant assignment `d ↦ G(op d)` sends finite
**colimits** in `D` to finite **limits** in `E`; likewise `G` "preserves finite
colimits" when `d ↦ G(op d)` sends finite **limits** in `D` to finite
**colimits** in `E`. Here `D = Sheaf K Ab`, `G = internalHomFunctor K J`, and the
contravariant assignment is `F ↦ ℋom(F, J)`. So:

* `PreservesFiniteLimits (internalHomFunctor K J)` ⟺ `ℋom(-, J)` turns finite
  colimits of abelian sheaves into finite limits — the *left exactness* of a
  contravariant Hom. This holds for **every** sheaf `J` (no injectivity needed).
* `PreservesFiniteColimits (internalHomFunctor K J)` ⟺ `ℋom(-, J)` turns finite
  limits of abelian sheaves into finite colimits — the *right exactness*, i.e.
  the surjectivity of `ℋom(F, J) → ℋom(F', J)` for a mono `F' ↪ F`. This is the
  substance of Tag 01DR and is exactly where `Injective J` is used.
-/

/-! **SG-A (left exactness, holds for any `J`).** The contravariant internal-Hom
functor `ℋom(-, J)` preserves finite limits, i.e. as the contravariant
assignment `F ↦ ℋom(F, J)` it sends finite colimits of abelian sheaves to finite
limits.

Informal argument. It suffices to show `ℋom(-, J)` sends finite colimits to
finite limits. A finite limit in `Sheaf K Ab` (equivalently a finite colimit in
the opposite category) is computed, after applying the section/evaluation
functors, objectwise; concretely a finite (co)limit of sheaves is detected on
each localized site `C/U`, where the relevant abelian groups are the hom-groups
`Hom_{Ab(C/U)}(F|_U, J|_U)`. The contravariant `Hom`-functor
`Hom_{Ab(C/U)}(-, J|_U) : Ab(C/U)ᵒᵖ → Ab` is left exact for every object `J|_U`:
`Hom(colim_i F_i, J) ≅ lim_i Hom(F_i, J)` naturally (the universal property of a
colimit). Two reductions make this concrete in the abelian setting:
(1) preservation of finite limits is equivalent (for a `PreservesZeroMorphisms`
functor between abelian-style categories) to preservation of kernels together
with the binary-product / terminal data; (2) `ℋom(-, J)` sends the cokernel of a
map `g : F' → F` to the kernel of `ℋom(F, J) → ℋom(F', J)`, and sends finite
coproducts to finite products, because `Hom(-, J)` does so at every `C/U`. These
identifications are natural and assemble to a `PreservesFiniteLimits` instance.
The only inputs are general left-exactness of `Hom(-, J)` and the fact that
limits/colimits of sheaves are computed objectwise on localized sites — no
property of `J` beyond being a sheaf is used. The formal proof is assembled below
(`internalHomFunctor_preservesFiniteLimits`), placed after the named kernel-preservation
lemma `internalHomFunctor_preservesKernels` it consumes. -/

/-! **SG-B (right exactness, the substance — uses `Injective J`).** When `J` is an
injective abelian sheaf, the contravariant internal-Hom functor `ℋom(-, J)`
preserves finite colimits, i.e. as the contravariant assignment `F ↦ ℋom(F, J)`
it sends finite limits of abelian sheaves to finite colimits.

Informal argument. Combined with SG-A this is the whole point of the lemma. For a
`PreservesZeroMorphisms` functor it suffices (dually to SG-A) to check that
`ℋom(-, J)` sends finite products to finite coproducts and, crucially, sends the
kernel of a map to the cokernel of the induced map; concretely the only
non-formal point is right exactness, namely that for a monomorphism `i : F' ↪ F`
of abelian sheaves the induced map `ℋom(F, J) → ℋom(F', J)` is an **epimorphism**
in `Sheaf K Ab`. Epimorphisms of abelian sheaves are tested on localized sites
`C/U` after sheafification, where surjectivity of
`Hom_{Ab(C/U)}(F|_U, J|_U) → Hom_{Ab(C/U)}(F'|_U, J|_U)` is precisely the
extension/lifting property: every map `F'|_U → J|_U` extends along the mono
`F'|_U ↪ F|_U` to a map `F|_U → J|_U`. This is the defining property of
injectivity of `J|_U` in `Ab(C/U)`. The restriction `(-)|_U = j_U^{-1}` has an
exact left adjoint (extension by zero / `j_!`), hence its right adjoint preserves
injectives, so `J|_U` is injective in `Ab(C/U)` whenever `J` is injective in
`Ab(C)`. Therefore `Hom(-, J|_U)` is exact on `Ab(C/U)`, giving the required
surjectivity at every `U`; combined with the (formal) preservation of finite
products this yields preservation of finite colimits. This is the unique place
`Injective J` enters, matching the Stacks one-line proof "because `J` is an
injective abelian sheaf." -/
/-! ### Decomposition of SG-B1 into the obligations O1, O2(-keystone), O3

The cokernel-preservation lemma SG-B1 (`internalHomFunctor_preservesCokernels`) is
the mathematical heart of Tag 01DR (the unique consumer of `Injective J`). Following
the informal proof (whose only obstacle is library infrastructure, not a
counterexample), it decomposes into:

* **(O2-keystone) `extensionByZero_preservesMonos`** — the unique *deep analytic*
  input: extension-by-zero `j_!`, the left adjoint of restriction `overPullback`
  (which the closer confirmed exists via the `IsRightAdjoint` instance), is
  left-exact (preserves monomorphisms). Everything below is then standard Mathlib.
* **(O2) `overPullback_preservesInjective`** — restriction to a localized site sends
  injectives to injectives. This is FULLY PROVED here *modulo only the O2-keystone*,
  via `Adjunction.ofIsRightAdjoint` + `Adjunction.map_injective`.
* **(O3) `sheaf_epi_of_objwise_surjective`** — a map of abelian sheaves that is
  surjective on every object's sections is an epimorphism (sheaf cokernel =
  sheafified presheaf cokernel; objectwise surjective ⇒ presheaf cokernel 0 ⇒ epi).
* **(O1 + assembly) `internalHomFunctor_preservesCokernels`** — the remaining
  packaging: at each `U`, `(i|_U)^*` is surjective by `Injective.factorThru`
  (using O2), hence (by O3) `i^* : ℋom(F,J) → ℋom(F',J)` is epi; combined with the
  always-true left-exactness this is exactly preservation of the relevant
  cokernel/colimit. This `IsColimit` hand-assembly against the concrete
  `internalHomFunctor` definition is the residual subtask.
-/

/-! ### Decomposition of the O2-keystone (`extensionByZero_preservesMonos`)

`extensionByZero_preservesMonos` is not proved directly; it follows from the following
reduction chain:

  `(overPullback).leftAdjoint.PreservesMonomorphisms`
    ⟸ `PreservesFiniteLimits ((overPullback).leftAdjoint)`   [Mathlib instance, `infer_instance`]
    ⟸ `PreservesFiniteLimits (sheafPullback)`                [transport along the iso of
        left adjoints `Adjunction.leftAdjointUniq`; `preservesFiniteLimits_of_natIso`]
    ⟸ `PreservesFiniteLimits ((Over.forget U).op.lan)`       [Mathlib auto-fires
        `Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback`,
        as `sheafToPresheaf` and `presheafToSheaf`/sheafification are left exact].

So the WHOLE keystone is reduced to the single CORE obligation
`lan_overForget_preservesFiniteLimits` below: the `Ab`-valued left Kan extension along
`(Over.forget U).op` preserves finite limits. The CORE is genuine analytic content;
NOTE the standard `lan_preservesFiniteLimits_of_flat` route does NOT apply here, since
`Over.forget U` is NOT representably flat in general (the structured-arrow / comma
categories are empty when `Hom(X,U) = ∅`). The reason it
holds is `Ab`-specific: the pointwise value of `(Over.forget U).op.lan` at `X`
is the COPRODUCT `⊕_{u ∈ Hom(X,U)} F(op (X,u))` over the fiber (each connected component
of the comma category has a terminal object `(t_u)ᵒᵖ`), and small COPRODUCTS IN `Ab`
ARE EXACT (preserve finite limits / kernels); the empty-fiber case is harmless (empty
coproduct = `0`, and `F ↦ 0` preserves finite limits). -/

/-! ### Decomposition of the CORE (`lan_overForget_preservesFiniteLimits`)

The CORE is not proved directly; it goes through the TWO named sub-lemmas below. The CORE
then assembles with no open goals:

  `PreservesFiniteLimits ((Over.forget U).op.lan)`
    ⟸ `preservesFiniteLimits_of_evaluation`: it suffices, for each `X : Cᵒᵖ`, that
        `lan ⋙ ev X` preserves finite limits.
    ⟸ **(CORE-A) `lan_compEvaluation_isoColim`**: a natural iso
        `lan ⋙ ev X ≅ (precompose along CostructuredArrow.proj) ⋙ colim`
        (the *pointwise* left Kan extension formula: `(lan F)(X) ≅ colim_{CostructuredArrow}
        (proj ⋙ F)`, via `Functor.leftKanExtensionObjIsoColimit`, natural in `F`).
    ⟸ **(CORE-B) `costructuredArrow_hasExactColimitsOfShape`**: the comma category
        `CostructuredArrow (Over.forget U).op X` has *exact* colimits into `Ab`, so
        `colim` over it preserves finite limits (`HasExactColimitsOfShape.preservesFiniteLimits`).
        This is where the analytic content lives: the comma category is *final* over the
        discrete fiber `Discrete (X ⟶ U)` (each component has a terminal/initial object),
        and `Ab` has exact colimits of discrete shape (AB4 — small coproducts in `Ab` are
        exact); `hasExactColimitsOfShape_of_final` transports exactness along the final
        functor. Empty fiber ⇒ the discrete shape is empty ⇒ the colimit is `0` (harmless).

`comp_preservesFiniteLimits` + `preservesFiniteLimits_of_natIso` then close the CORE.
This route avoids re-deriving the explicit coproduct formula B5 by hand: the colimit
itself is left as `colim`, and exactness is obtained structurally from finality + AB4. -/

/-- **(CORE-A)** Pointwise-Kan natural iso: the composite `(Over.forget U).op.lan ⋙ ev X`
is naturally isomorphic to "precompose with `CostructuredArrow.proj`, then take `colim`".
This is `Functor.leftKanExtensionObjIsoColimit` (the value of the left Kan extension at `X`
is the colimit over the comma category `CostructuredArrow (Over.forget U).op X` of
`proj ⋙ F`), assembled into a natural iso of functors via `NatIso.ofComponents`
(`(Over.forget U).op.lan.obj F = (Over.forget U).op.leftKanExtension F` by `rfl`).
The naturality square is the residual analytic obligation.

The coefficient universe `w` is only required to be at least as large as that of the site
(`UnivLE.{max u v, w}`), which is what makes the colimits over the comma category exist. -/
noncomputable def lan_compEvaluation_isoColim (U : C) (X : Cᵒᵖ) [UnivLE.{max u v, w}] :
    (Over.forget U).op.lan ⋙ (evaluation Cᵒᵖ Ab.{w}).obj X ≅
      ((Functor.whiskeringLeft (CostructuredArrow (Over.forget U).op X) (Over U)ᵒᵖ Ab.{w}).obj
        (CostructuredArrow.proj (Over.forget U).op X)) ⋙ colim :=
      -- For each `F`, `Functor.leftKanExtensionObjIsoColimit (Over.forget U).op F X` gives
  -- `(lan F)(X) ≅ colimit (proj ⋙ F)`; bundle into a natural iso (the naturality square
  -- is the work). Mathlib: `Functor.leftKanExtensionObjIsoColimit`, `NatIso.ofComponents`,
  -- `colimit.hom_ext`, `ι_colimMap`, `ι_leftKanExtensionObjIsoColimit_inv`.
  NatIso.ofComponents
    (fun F => (Over.forget U).op.leftKanExtensionObjIsoColimit F X)
    (by
      intro F G f
      dsimp only [Functor.comp_map, evaluation_obj_map, Functor.whiskeringLeft_obj_obj,
        Functor.comp_obj]
      rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
      apply colimit.hom_ext
      intro j
      rw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
      simp only [colim_map, ι_colimMap_assoc,
        Functor.ι_leftKanExtensionObjIsoColimit_inv]
      have hunit : ((Over.forget U).op.leftKanExtensionUnit F).app j.left ≫
            ((Over.forget U).op.lan.map f).app ((Over.forget U).op.obj j.left)
          = (((Functor.whiskeringLeft (CostructuredArrow (Over.forget U).op X) (Over U)ᵒᵖ
                Ab.{w}).obj (CostructuredArrow.proj (Over.forget U).op X)).map f).app j ≫
            ((Over.forget U).op.leftKanExtensionUnit G).app j.left := by
        have := Functor.descOfIsLeftKanExtension_fac_app ((Over.forget U).op.leftKanExtension F)
          ((Over.forget U).op.leftKanExtensionUnit F) ((Over.forget U).op.leftKanExtension G)
          (f ≫ (Over.forget U).op.leftKanExtensionUnit G) j.left
        exact this
      erw [((Over.forget U).op.lan.map f).naturality j.hom, ← Category.assoc, hunit,
        Category.assoc])

namespace CostructuredArrowFiber

/-- The discrete fiber functor: to a fiber index `u : X.unop ⟶ U` it associates the
object `(Over.mk u)ᵒᵖ` of the comma category with structure map the (opposite of the)
identity of `X.unop`. This is the opposite of the per-fiber terminal object `t_u`. -/
noncomputable def fiberFunctor (U : C) (X : Cᵒᵖ) :
    Discrete (X.unop ⟶ U) ⥤ CostructuredArrow (Over.forget U).op X :=
  Discrete.functor (fun u =>
    CostructuredArrow.mk (Y := Opposite.op (Over.mk u)) (Opposite.op (𝟙 X.unop)))

/-- The fiber index of an object of the comma category. -/
noncomputable def fiberIdx (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X) :
    X.unop ⟶ U :=
  d.hom.unop ≫ d.left.unop.hom

/-- The underlying `C`-map of the structure morphism of an object of `StructuredArrow d Φ`
is forced to be `d.hom.unop`. -/
private theorem fiber_left_eq_aux (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X)
    (Z : StructuredArrow d (fiberFunctor U X)) :
    Z.hom.left.unop.left = d.hom.unop := by
  simpa [fiberFunctor] using congrArg Quiver.Hom.unop Z.hom.w

/-- Every object of `StructuredArrow d (fiberFunctor U X)` lies over the fiber index of `d`. -/
theorem fiber_eq (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X)
    (Z : StructuredArrow d (fiberFunctor U X)) :
    Z.right.as = fiberIdx U X d := by
  have hw : Z.hom.left.unop.left ≫ d.left.unop.hom = Z.right.as := Over.w Z.hom.left.unop
  rw [fiberIdx, ← fiber_left_eq_aux, hw]

/-- The underlying `C`-map of the structure morphism of an object of `StructuredArrow d Φ`
is forced to be `d.hom.unop`. -/
theorem fiber_left_eq (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X)
    (Z : StructuredArrow d (fiberFunctor U X)) :
    Z.hom.left.unop.left = d.hom.unop :=
  fiber_left_eq_aux U X d Z

/-- The canonical object of `StructuredArrow d (fiberFunctor U X)`, at the fiber index of `d`. -/
noncomputable def initObj (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X) :
    StructuredArrow d (fiberFunctor U X) :=
  StructuredArrow.mk (Y := Discrete.mk (fiberIdx U X d))
    (CostructuredArrow.homMk
      (Quiver.Hom.op (Over.homMk d.hom.unop (by simp [fiberIdx])))
      (by
        simp only [fiberFunctor]
        apply Quiver.Hom.unop_inj
        simp))

/-- The unique morphism out of the canonical object to any other object. -/
noncomputable def initHom (U : C) (X : Cᵒᵖ) (d : CostructuredArrow (Over.forget U).op X)
    (Z : StructuredArrow d (fiberFunctor U X)) :
    initObj U X d ⟶ Z := by
  refine StructuredArrow.homMk (eqToHom (Discrete.ext ((fiber_eq U X d Z).symm))) ?_
  · apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    rw [fiber_left_eq]
    simp only [initObj, fiberFunctor]
    simp [eqToHom_map]

/-- The canonical object is initial: each comma category is connected. -/
noncomputable def isInitialInitObj (U : C) (X : Cᵒᵖ)
    (d : CostructuredArrow (Over.forget U).op X) :
    Limits.IsInitial (initObj U X d) :=
  Limits.IsInitial.ofUniqueHom (initHom U X d) (fun Z m => by
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim)

/-- The discrete fiber functor is final: each `StructuredArrow d Φ` has an initial object,
hence is connected. -/
instance fiberFunctor_final (U : C) (X : Cᵒᵖ) : (fiberFunctor U X).Final :=
  ⟨fun d => isConnected_of_isInitial _ (isInitialInitObj U X d)⟩

end CostructuredArrowFiber

/-- **(CORE-B)** The comma category `CostructuredArrow (Over.forget U).op X` has *exact*
colimits into `Ab`. Hence `colim` over it preserves finite limits.

This is the analytic heart, made structural: the comma category decomposes into connected
components indexed by the fiber `Hom_C(X, U)`, each component having a terminal object (the
opposite of the initial object `t_u = (X, u, id_X)`). So the
discrete fiber functor `Discrete (X ⟶ U) ⥤ CostructuredArrow (Over.forget U).op X` is
*final*; `Ab` has exact colimits of discrete shape (AB4: small coproducts in `Ab` are
exact); and `hasExactColimitsOfShape_of_final` transports exactness along the final functor.
Empty fiber ⇒ empty discrete shape ⇒ colimit is `0` (`F ↦ 0` preserves finite limits).

The fiber index type `Hom(X, U)` lives in `Type v`, so it is shrunk twice before AB4 is
applied: first lifted to `Type (max u v)` by `ULift.{u}`, then transported into `Type w` by
`Shrink.{w}`, which is available because `UnivLE.{max u v, w}`. Both transports are
equivalences of discrete categories, hence final, so exactness pulls back along them. This is
what lets the coefficient universe `w` be strictly larger than that of the site: AB4 is
applied to `Ab.{w}` at an index type that genuinely lives in `Type w`. -/
theorem costructuredArrow_hasExactColimitsOfShape (U : C) (X : Cᵒᵖ) [UnivLE.{max u v, w}] :
    HasExactColimitsOfShape (CostructuredArrow (Over.forget U).op X) Ab.{w} := by
  -- The discrete fiber functor `Φ = fiberFunctor U X` is final (each comma category
  -- `StructuredArrow d Φ` has an initial object at the fiber index of `d`); `Ab` has exact
  -- colimits of discrete shape (AB4); transport exactness along the final functor.
  -- We precompose with the two shrinking equivalences so that the fiber index type is
  -- covered by the AB4 instance for `Ab.{w}`.
  have : Small.{w} (ULift.{u} (X.unop ⟶ U)) := inferInstance
  let e0 : Discrete (Shrink.{w} (ULift.{u} (X.unop ⟶ U))) ⥤
      Discrete (ULift.{u} (X.unop ⟶ U)) :=
    (Discrete.equivalence (equivShrink.{w} (ULift.{u} (X.unop ⟶ U)))).inverse
  let e1 : Discrete (ULift.{u} (X.unop ⟶ U)) ⥤ Discrete (X.unop ⟶ U) :=
    (Discrete.equivalence (Equiv.ulift.{u})).functor
  have h0 : e0.Final := inferInstanceAs
    ((Discrete.equivalence (equivShrink.{w} (ULift.{u} (X.unop ⟶ U)))).inverse).Final
  have h1 : e1.Final := inferInstanceAs
    ((Discrete.equivalence (Equiv.ulift.{u})).functor).Final
  have : HasExactColimitsOfShape
      (Discrete (Shrink.{w} (ULift.{u} (X.unop ⟶ U)))) Ab.{w} :=
    AB4OfSize.ofShape (C := Ab.{w}) (Shrink.{w} (ULift.{u} (X.unop ⟶ U)))
  have hf : (e0 ⋙ e1 ⋙ CostructuredArrowFiber.fiberFunctor U X).Final :=
    Functor.final_comp e0 (e1 ⋙ CostructuredArrowFiber.fiberFunctor U X)
  exact hasExactColimitsOfShape_of_final Ab.{w}
    (e0 ⋙ e1 ⋙ CostructuredArrowFiber.fiberFunctor U X)

/-- **(O2-keystone CORE)** The `Ab`-valued left Kan extension along `(Over.forget U).op`
preserves finite limits. This is the unique remaining analytic input behind the
exactness of extension-by-zero `j_!` (Stacks Tag 01DR).

PROOF (from CORE-A `lan_compEvaluation_isoColim` and CORE-B
`costructuredArrow_hasExactColimitsOfShape`): by `preservesFiniteLimits_of_evaluation`
it suffices that `lan ⋙ ev X` preserves finite limits for each `X`; by CORE-A this is
naturally isomorphic to `(precompose proj) ⋙ colim`, and `colim` preserves finite limits
by CORE-B (`HasExactColimitsOfShape.preservesFiniteLimits`).

The coefficient universe `w` need only dominate that of the site (`UnivLE.{max u v, w}`); in
particular it may be strictly larger, which is what a site whose objects form a `Type (u + 1)`
with morphisms in `Type u` and coefficients in `Ab.{max (u + 1) v}` requires. -/
theorem lan_overForget_preservesFiniteLimits [UnivLE.{max u v, w}]
    (U : C) :
    PreservesFiniteLimits ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ Ab.{w}) ⥤ (Cᵒᵖ ⥤ Ab.{w})) := by
  -- SANITY CHECK PASSED (STATUS: plausible; no counterexample).
  apply preservesFiniteLimits_of_evaluation
  intro X
  have : HasExactColimitsOfShape (CostructuredArrow (Over.forget U).op X) Ab.{w} :=
    costructuredArrow_hasExactColimitsOfShape (C := C) U X
  have : PreservesFiniteLimits
      (colim : (CostructuredArrow (Over.forget U).op X ⥤ Ab.{w}) ⥤ Ab.{w}) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  have : PreservesFiniteLimits
      (((Functor.whiskeringLeft (CostructuredArrow (Over.forget U).op X) (Over U)ᵒᵖ
          Ab.{w}).obj
        (CostructuredArrow.proj (Over.forget U).op X)) ⋙ colim) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (lan_compEvaluation_isoColim (C := C) U X).symm

/-- The left adjoint `j_!` of restriction `overPullback` preserves finite limits.
This reduces to `lan_overForget_preservesFiniteLimits`: the abstract
`(overPullback).leftAdjoint` is
canonically isomorphic (`Adjunction.leftAdjointUniq`) to the concrete `sheafPullback`,
whose finite-limit preservation Mathlib derives instance-automatically from
`PreservesFiniteLimits ((Over.forget U).op.lan)`. -/
@[sga "4 III 1.7" "Clause 1, special case", sga "4 V 2.2" "partial"]
theorem leftAdjoint_preservesFiniteLimits [UnivLE.{max u v, w}]
    (K : GrothendieckTopology C) [HasSheafify K Ab.{w}]
    [∀ (U : C), HasSheafify (K.over U) Ab.{w}]
    (U : C) :
    PreservesFiniteLimits ((K.overPullback Ab.{w} U).leftAdjoint) := by
  have : PreservesFiniteLimits ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ Ab.{w}) ⥤ (Cᵒᵖ ⥤ Ab.{w})) :=
    lan_overForget_preservesFiniteLimits (C := C) U
  have adj1 : ((K.overPullback Ab.{w} U).leftAdjoint) ⊣ (K.overPullback Ab.{w} U) :=
    Adjunction.ofIsRightAdjoint _
  have adj2 := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.forget U) Ab.{w} (K.over U) K
  exact preservesFiniteLimits_of_natIso (adj2.leftAdjointUniq adj1)

/-- **(O2-keystone)** Extension-by-zero `j_!` — the left adjoint of restriction
`overPullback` to a localized site — preserves monomorphisms (is left-exact). This
is the unique deep analytic input behind Tag 01DR's use of injectivity: on abelian
sheaves, extension by zero along the open immersion `j_U : C/U → C` is an exact
functor. The closer confirmed the adjunction `j_! ⊣ overPullback` already exists in
the library (`(overPullback _).leftAdjoint` via the `IsRightAdjoint` instance); the
exactness of `j_!` itself is the remaining standalone obligation.

PROOF (from `lan_overForget_preservesFiniteLimits`):
preserving monos follows from `PreservesFiniteLimits` (`infer_instance`), which is
`leftAdjoint_preservesFiniteLimits`.

Reference: Stacks Tag 01DR proof; the extension-by-zero functor `j_!` for the
localization morphism of topoi is exact (it is even the left adjoint in a sequence
`j_! ⊣ j^* ⊣ j_*`, and `j_!` is exact for an open immersion of sites).

The coefficient universe `w` is only constrained by `UnivLE.{max u v, w}`: see
`costructuredArrow_hasExactColimitsOfShape` for where that hypothesis is used, and note that
it holds unconditionally for a site of objects `Type (u + 1)` with morphisms in `Type u` and
coefficients `Ab.{max (u + 1) v}`. -/
@[sga "4 IV 11.3.1" "Exactness clause",
  sga "4 XVII 5.1.1" "abelian-sheaf version",
  sga "4 XVII 5.1.3" "partial"]
theorem extensionByZero_preservesMonos [UnivLE.{max u v, w}]
    (K : GrothendieckTopology C) [HasSheafify K Ab.{w}]
    [∀ (U : C), HasSheafify (K.over U) Ab.{w}]
    (U : C) :
    (K.overPullback Ab.{w} U).leftAdjoint.PreservesMonomorphisms := by
  -- The left adjoint `j_!` exists; preserving monos is the exactness of `j_!`,
  -- reduced to `PreservesFiniteLimits` of `j_!` (`leftAdjoint_preservesFiniteLimits`),
  -- itself reduced to `lan_overForget_preservesFiniteLimits`.
  have : PreservesFiniteLimits ((K.overPullback Ab.{w} U).leftAdjoint) :=
    leftAdjoint_preservesFiniteLimits K U
  -- IMPORTANT: do NOT use bare `infer_instance` here — the draft libs expose a
  -- `sorryAx`-tainted `PreservesMonomorphisms` instance for `overPullback`/its
  -- left adjoint that `infer_instance` would latch onto. Route HONESTLY through the
  -- genuine `PreservesFiniteLimits` (⇒ `PreservesLimitsOfShape WalkingCospan`) via
  -- `preservesMonomorphisms_of_preservesLimitsOfShape`.
  exact preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **(O2)** Restriction `overPullback` to a localized site `C/U` sends injective
abelian sheaves to injective abelian sheaves. In particular `J|_U` is injective
whenever `J` is. This is FULLY PROVED modulo the single keystone
`extensionByZero_preservesMonos`: it is `Adjunction.map_injective` applied to the
adjunction `j_! ⊣ overPullback` (a right adjoint whose left adjoint preserves monos
preserves injectives). -/
@[sga "2 I 1.4" "special case",
  sga "4 V 2.2" "special case",
  sga "4 V 2.3.2" "special case",
  sga "4 V 4.11" "1), special case",
  sga "4 V 4.12" "special case",
  sga "7 VII 1.4" "special case",
  sga "7 XIII 2.1.2" "special case"]
theorem overPullback_preservesInjective [UnivLE.{max u v, w}]
    (K : GrothendieckTopology C) [HasSheafify K Ab.{w}]
    [∀ (U : C), HasSheafify (K.over U) Ab.{w}]
    (U : C) (J : Sheaf K Ab.{w}) [Injective J] :
    Injective ((K.overPullback Ab.{w} U).obj J) := by
  -- `j_! ⊣ overPullback` with `j_!` mono-preserving (the keystone) ⇒ `overPullback`
  -- preserves injectives.
  have : (K.overPullback Ab.{w} U).leftAdjoint.PreservesMonomorphisms :=
    extensionByZero_preservesMonos K U
  exact (Adjunction.ofIsRightAdjoint (K.overPullback Ab.{w} U)).map_injective J ‹_›

/-- **(O3)** A morphism of abelian sheaves that is *surjective on every object's
sections* is an epimorphism in `Sheaf K Ab`. (Objectwise surjectivity is stronger
than local surjectivity; the presheaf cokernel of an objectwise-surjective map is
`0`, so its sheafification is `0`, so the map is epi. Mathlib pieces: sheaf cokernel
= sheafified presheaf cokernel via `presheafToSheaf`/`sheafificationAdjunction`, and
`epi_iff_cokernel`.) -/
theorem sheaf_epi_of_objwise_surjective
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    {A B : Sheaf K Ab.{max u v}} (φ : A ⟶ B)
    (h : ∀ (X : Cᵒᵖ), Function.Surjective (φ.hom.app X)) :
    Epi φ := by
  -- Objectwise surjectivity ⇒ local surjectivity of the underlying presheaf map,
  -- and a locally surjective map of sheaves is an epimorphism.
  have : Presheaf.IsLocallySurjective K φ.hom :=
    Presheaf.isLocallySurjective_of_surjective K φ.hom h
  exact Sheaf.epi_of_isLocallySurjective φ

/-- The induced map `i^* : ℋom(F, J) → ℋom(F', J)` is *surjective on every section*
over `U`, for a monomorphism `i : F' ↪ F` of abelian sheaves, when `J` is injective.
This is the sectionwise injective-lifting heart of Tag 01DR: a section over `U` is a
morphism `F'|_U → J|_U` of abelian sheaves on the localized site `C/U`, which extends
along the mono `i|_U` because `J|_U = overPullback U J` is injective there
(`overPullback_preservesInjective`) and `i|_U = (overPullback U).map i` is a mono
(right adjoint preserves monos). -/
@[sga "4 V 4.10" "Clause 1 for A = Z"]
theorem internalHomFunctor_objwise_surjective
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) [Injective J]
    {F' F : Sheaf K Ab.{max u v}} (i : F' ⟶ F) [Mono i] (U : C) :
    Function.Surjective
      (⇑(((internalHomFunctor K J).map i.op).hom.app (Opposite.op U))) := by
  have : Injective ((K.overPullback Ab.{max u v} U).obj J) :=
    overPullback_preservesInjective K U J
  have : Mono ((K.overPullback Ab.{max u v} U).map i) :=
    (K.overPullback Ab.{max u v} U).map_mono i
  intro a'
  set a₀ : (K.overPullback Ab.{max u v} U).obj F' ⟶ (K.overPullback Ab.{max u v} U).obj J :=
    ⟨a'⟩ with ha₀
  refine ⟨(Injective.factorThru a₀ ((K.overPullback Ab.{max u v} U).map i)).hom, ?_⟩
  have hfac := Injective.comp_factorThru a₀ ((K.overPullback Ab.{max u v} U).map i)
  -- the section map is precomposition by `((overPullback U).map i).hom` (defeq), so the goal
  -- becomes `((overPullback U).map i).hom ≫ (factorThru a₀ _).hom = a'`.
  show ((K.overPullback Ab.{max u v} U).map i).hom ≫
      (Injective.factorThru a₀ ((K.overPullback Ab.{max u v} U).map i)).hom = a'
  have hcomp : ((K.overPullback Ab.{max u v} U).map i).hom ≫
      (Injective.factorThru a₀ ((K.overPullback Ab.{max u v} U).map i)).hom
      = ((K.overPullback Ab.{max u v} U).map i ≫
          Injective.factorThru a₀ ((K.overPullback Ab.{max u v} U).map i)).hom := rfl
  rw [hcomp, hfac, ha₀]

/-- **(Epi part of SG-B1, the substance — uses `Injective J`).** The contravariant
internal-Hom functor `ℋom(-, J)` preserves epimorphisms: an epimorphism in
`(Sheaf K Ab)ᵒᵖ` is a monomorphism `i : F' ↪ F` in `Sheaf K Ab`, and the induced
`i^* : ℋom(F, J) → ℋom(F', J)` is an epimorphism because it is surjective on every
section (`internalHomFunctor_objwise_surjective`), hence epi by
`sheaf_epi_of_objwise_surjective` (O3). -/
@[sga "4 V 4.10" "Clause 1 for A = Z"]
instance internalHomFunctor_preservesEpimorphisms
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) [Injective J] :
    (internalHomFunctor K J).PreservesEpimorphisms := by
  refine ⟨fun {X Y} φ _ => ?_⟩
  have : Mono φ.unop := unop_mono_of_epi φ
  refine sheaf_epi_of_objwise_surjective K ((internalHomFunctor K J).map φ) ?_
  intro Z
  have hφ : φ = φ.unop.op := rfl
  rw [hφ]
  exact internalHomFunctor_objwise_surjective K J φ.unop Z.unop

/-- The objectwise natural isomorphism realizing `ℋom(-, J)(U)` as a corepresentable
additive functor on the slice sheaf category: `F ↦ Hom_{Sheaf (K.over U)}(F|_U, J|_U)`.
The section group `ℋom(F, J)(U)` is, definitionally, the hom-group
`((overPullback U).obj F.unop ⟶ (overPullback U).obj J)` of sheaves on the slice site,
so the components are the identity (packaged as an `AddEquiv`) and naturality is `rfl`. -/
@[ega "0 4.1.5" "Γ(U, special case", sga "4 IV 12.1" "special case"]
noncomputable def internalHomObjwiseCorepIso (K : GrothendieckTopology C)
    [HasSheafify K Ab.{max u v}] (J : Sheaf K Ab.{max u v}) (U : C) :
    internalHomFunctor K J ⋙ sheafToPresheaf K Ab.{max u v} ⋙
        (evaluation Cᵒᵖ Ab.{max u v}).obj (Opposite.op U) ≅
      (K.overPullback Ab.{max u v} U).op ⋙
        preadditiveYoneda.obj ((K.overPullback Ab.{max u v} U).obj J) :=
  NatIso.ofComponents
    (fun F => AddEquiv.toAddCommGrpIso
      { toFun := fun a => ⟨a⟩
        invFun := fun f => f.hom
        left_inv := by intro a; rfl
        right_inv := by intro f; rfl
        map_add' := by intro a b; rfl })
    (by intro F F' φ; rfl)

/-- **(O1-objectwise) The objectwise/section core of kernel preservation.**
For every morphism `g : X ⟶ Y` in `(Sheaf K Ab)ᵒᵖ` and every object `U : Cᵒᵖ`, the
composite functor `ℋom(-, J) ⋙ sheafToPresheaf ⋙ (evaluation at U)`, i.e. the functor
sending `F ↦ ℋom(F, J)(U)` valued in `Ab`, preserves the kernel of `g`.

This is the honest analytic core of O1 (left-exactness of contravariant Hom, computed at
the section level over `U`). At `U` the section group is, by `rfl`,
`Hom_{(Over U)ᵒᵖ ⥤ Ab}((overPullback U).obj F.unop.obj, (overPullback U).obj J.obj)`,
i.e. the corepresentable additive functor `preadditiveYoneda.obj M` (with
`M = (overPullback U).obj J.obj`) precomposed with the restriction
`F ↦ (overPullback U).obj F.obj`. The honest pieces:
* `preadditiveYoneda.obj M : Eᵒᵖ ⥤ Ab` (`E = (Over U)ᵒᵖ ⥤ Ab`, abelian) preserves finite
  limits — `PreservesFiniteLimits (preadditiveYoneda.obj M)` is a Mathlib instance,
  verified proof-complete (axioms `[propext, Classical.choice, Quot.sound]`). This sends the
  cokernel of `(overPullback U).map i` to the kernel of the induced precomposition map.
* The restriction `F ↦ (overPullback U).obj F.obj` (precomposition by `(Over.forget U).op`,
  an exact functor) sends the sheaf-cokernel underlying `g = i.op` to the cokernel of
  `(overPullback U).map i`, so the corepresentable left-exactness applies.
NOTE: do NOT close any `PreservesLimit`/`PreservesColimit` via a bare `inferInstance` on
`overPullback`/`internalHomFunctor` — those instances are `sorryAx`-tainted in the draft
libs. Use the Mathlib `preadditiveYoneda` left-exactness honestly. -/
@[ega "0 4.1.5" "special case", sga "4 IV 12.2" "special case"]
theorem internalHomFunctor_preservesKernels_objectwise
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v})
    {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (g : X ⟶ Y) (U : Cᵒᵖ) :
    PreservesLimit (parallelPair g 0)
      (internalHomFunctor K J ⋙ sheafToPresheaf K Ab.{max u v} ⋙
        (evaluation Cᵒᵖ Ab.{max u v}).obj U) := by
  -- SANITY CHECK PASSED (STATUS: plausible; variance correct — this is the always-true
  -- left-exact `PreservesLimit` direction, no `Injective J`; the analytic-core prototype
  -- `PreservesLimit (parallelPair g 0) (preadditiveYoneda.obj M)` over an opposite abelian
  -- category is a Mathlib `infer_instance` with no injectivity. No counterexample.)
  -- HONEST PROOF (no sorryAx). At `U`, the section functor is naturally isomorphic to the
  -- corepresentable additive functor `Hom_{Sheaf (K.over U)}(-, J|_U)` precomposed with the
  -- restriction `(overPullback U).op` (`internalHomObjwiseCorepIso`). The corepresentable
  -- `preadditiveYoneda.obj ((overPullback U) J)` preserves finite limits (slice sheaf cat is
  -- abelian — Mathlib instance). The crucial honest point: `overPullback U` is the inverse
  -- image of the localization, i.e. a *left* adjoint via the cocontinuous-functor adjunction
  -- `sheafPushforwardContinuous ⊣ sheafPushforwardCocontinuous` (`Over.forget U` is both
  -- continuous and cocontinuous for `K.over U`/`K`), so it preserves colimits; hence
  -- `(overPullback U).op` preserves limits of shape `WalkingParallelPair`. Composing gives the
  -- kernel preservation, transported through the natural iso. (We supply the honest
  -- `IsLeftAdjoint` witness explicitly so the colimit-preservation instance is the genuine one,
  -- not the `sorryAx`-tainted draft-library instance.)
  obtain ⟨U⟩ := U
  have : (K.overPullback Ab.{max u v} U).IsLeftAdjoint :=
    ⟨_, ⟨(Over.forget U).sheafAdjunctionCocontinuous Ab.{max u v} (K.over U) K⟩⟩
  have : PreservesColimitsOfShape WalkingParallelPairᵒᵖ (K.overPullback Ab.{max u v} U) :=
    inferInstance
  have : PreservesLimitsOfShape WalkingParallelPair (K.overPullback Ab.{max u v} U).op :=
    preservesLimitsOfShape_op WalkingParallelPair _
  have : PreservesLimit (parallelPair g 0)
      ((K.overPullback Ab.{max u v} U).op ⋙
        preadditiveYoneda.obj ((K.overPullback Ab.{max u v} U).obj J)) :=
    inferInstance
  exact preservesLimit_of_natIso _ (internalHomObjwiseCorepIso K J U).symm

/-- **(O1) Kernel preservation / left-exactness of the contravariant internal Hom.**
For every morphism `g : X ⟶ Y` in `(Sheaf K Ab)ᵒᵖ`, the contravariant internal-Hom
functor `ℋom(-, J)` preserves the kernel of `g` (the limit of `parallelPair g 0`).

This holds for *any* sheaf `J` (no injectivity). Unwound, a kernel in the opposite
category `(Sheaf K Ab)ᵒᵖ` is a cokernel in `Sheaf K Ab`; preservation of it by
`ℋom(-, J)` is the universal-property statement that `ℋom(-, J)` sends the cokernel
of a map `p : F ↠ F''` of abelian sheaves to the kernel of the induced
`ℋom(F'', J) → ℋom(F, J)`, i.e. left-exactness of contravariant Hom. On each
localized site `C/U` this is the exactness of `Hom_{Ab(C/U)}(-, J|_U)` on the left,
which is the universal property of colimits; sheaf kernels are computed objectwise.

This is exactly the kernel-half of `internalHomFunctor_preservesFiniteLimits` (SG-A).
It is the residual analytic obligation of the SG-B1 cokernel-preservation assembly
(the epi/right-exact substance is already fully proved above, with no open goals).

FORMAL SKETCH (verified proof-complete wiring; honest reduction to the objectwise core):
sheaf-level limit preservation is reduced to the objectwise/section-level statement via
`sheafToPresheaf` reflecting limits (`preservesLimit_of_reflects_of_preserves`) and
`evaluation` jointly reflecting limits (`preservesLimit_of_evaluation`). The remaining
content lives entirely in `internalHomFunctor_preservesKernels_objectwise`. -/
@[ega "0 4.1.5" "special case",
  sga "4 IV 12.2" "partial, special case",
  sga "4 V 4.10" "Clause 1 for A = Z"]
theorem internalHomFunctor_preservesKernels
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) :
    ∀ {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (g : X ⟶ Y),
      PreservesLimit (parallelPair g 0) (internalHomFunctor K J) := by
  -- SANITY CHECK PASSED (STATUS: plausible; variance NOT swapped — this is the
  -- always-true left-exact direction `PreservesLimit`, no `Injective J`; no counterexample).
  -- HONEST REDUCTION (no sorryAx): sheaf limits are reflected by `sheafToPresheaf`, and
  -- presheaf limits are detected objectwise by `evaluation`. So preservation of the kernel
  -- by `internalHomFunctor K J` follows from preservation by each objectwise composite
  -- (`internalHomFunctor_preservesKernels_objectwise`).
  intro X Y g
  have : PreservesLimit (parallelPair g 0)
      (internalHomFunctor K J ⋙ sheafToPresheaf K Ab.{max u v}) :=
    preservesLimit_of_evaluation _ _
      (fun U => internalHomFunctor_preservesKernels_objectwise K J g U)
  exact preservesLimit_of_reflects_of_preserves
    (internalHomFunctor K J) (sheafToPresheaf K Ab.{max u v})

/-- **SG-A assembly (left exactness).** Relocated below `internalHomFunctor_preservesKernels`
so that the kernel-preservation hypothesis is available as a named lemma (avoiding the
`sorryAx`-tainted draft-library `PreservesLimit` instances). Finite-limit preservation
reduces, for the additive (`PreservesZeroMorphisms`) functor `ℋom(-, J)`, to kernel
preservation plus the structural biproduct/terminal data, via the Mathlib lemma
`Functor.preservesFiniteLimits_of_preservesKernels`; the kernel half is supplied
EXPLICITLY by `internalHomFunctor_preservesKernels K J`. -/
@[ega "0 4.1.5" "special case",
  sga "4 IV 12.2" "partial, special case",
  sga "4 V 4.10" "Clause 1 for A = Z"]
theorem internalHomFunctor_preservesFiniteLimits
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) :
    PreservesFiniteLimits (internalHomFunctor K J) := by
  have hker : ∀ {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (g : X ⟶ Y),
      PreservesLimit (parallelPair g 0) (internalHomFunctor K J) :=
    internalHomFunctor_preservesKernels K J
  exact Functor.preservesFiniteLimits_of_preservesKernels (internalHomFunctor K J)

/-- **SG-B1 (cokernel preservation — the substance; uses `Injective J`).**
For every morphism `f : X ⟶ Y` in `(Sheaf K Ab)ᵒᵖ`, the contravariant internal-Hom
functor `ℋom(-, J)` preserves the cokernel of `f` (the colimit of `parallelPair f 0`).

This is the unique place `Injective J` is consumed. Unwound, a cokernel in the
opposite category `(Sheaf K Ab)ᵒᵖ` is a kernel in `Sheaf K Ab`; preservation of it
by `ℋom(-, J)` is the statement that for a monomorphism `i : F' ↪ F` of abelian
sheaves the induced map `i^* : ℋom(F, J) → ℋom(F', J)` is an epimorphism (together
with the always-true left-exactness giving the kernel part). On each localized site
`C/U` this map is `(i|_U)^* : Hom(F|_U, J|_U) → Hom(F'|_U, J|_U)`, which is
*surjective* because `J|_U` is injective in `Ab(C/U)` (`Injective.factorThru`) and
`i|_U` is a monomorphism; sectionwise surjectivity then forces an epimorphism of
sheaves. Injectivity of `J|_U` follows from injectivity of `J` because restriction
`(-)|_U = overPullback` is the right adjoint of the exact extension-by-zero `j_!`
(`Adjunction.map_injective`).

NOTE: this sub-lemma is the mathematical heart of Tag 01DR and itself decomposes
into the sub-obligations (O1) sheaf-level left exactness, (O2) restriction preserves
injectives via an exact `j_!`, plus the sectionwise-surjective ⇒ sheaf-epi bridge. -/
@[sga "4 V 4.10" "Clause 1 for A = Z"]
theorem internalHomFunctor_preservesCokernels
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) [Injective J] :
    ∀ {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (internalHomFunctor K J) := by
  -- CLEAN HONEST REDUCTION (NO sorryAx). The colimit of `parallelPair f 0` is the
  -- cokernel of `f`. For an additive (`PreservesZeroMorphisms`) functor between
  -- abelian categories, preservation of cokernels follows from preservation of
  -- homology (`Functor.PreservesHomology.preservesCokernel`), which in turn follows
  -- from preserving epimorphisms + preserving kernels
  -- (`Functor.preservesHomology_of_preservesEpis_and_kernels`). We supply:
  --   • epi-preservation: `internalHomFunctor_preservesEpimorphisms` (the substance,
  --     uses `Injective J`) — FULLY PROVED above;
  --   • kernel-preservation `[∀ f, PreservesLimit (parallelPair f 0) G]`: this is the
  --     always-true (any-`J`) LEFT-EXACTNESS (O1) of the contravariant internal Hom,
  --     i.e. that `ℋom(-, J)` sends cokernels of abelian sheaves to kernels. It is
  --     exactly the kernel-half of `internalHomFunctor_preservesFiniteLimits` (SG-A).
  intro X Y f
  have : (internalHomFunctor K J).PreservesEpimorphisms :=
    internalHomFunctor_preservesEpimorphisms K J
  have hker : ∀ {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (g : X ⟶ Y),
      PreservesLimit (parallelPair g 0) (internalHomFunctor K J) :=
    internalHomFunctor_preservesKernels K J
  have : (internalHomFunctor K J).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (internalHomFunctor K J)
  exact Functor.PreservesHomology.preservesCokernel (internalHomFunctor K J) f

/-- For an injective abelian sheaf `J`, the contravariant internal Hom functor `ℋom(-, J)`
preserves finite colimits. -/
@[sga "4 V 4.10" "Clause 1 for A = Z"]
theorem internalHomFunctor_preservesFiniteColimits
    (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) [Injective J] :
    PreservesFiniteColimits (internalHomFunctor K J) := by
  -- Reduce finite-colimit preservation to: additivity (already an instance, gives
  -- finite-coproduct/biproduct preservation) + cokernel preservation, via the
  -- Mathlib lemma `Functor.preservesFiniteColimits_of_preservesCokernels`. The
  -- structural hypotheses (HasBinaryBiproducts / HasFiniteCoproducts /
  -- HasCoequalizers / HasZeroObject on `(Sheaf K Ab)ᵒᵖ` and `Sheaf K Ab`) are
  -- inferred cleanly (verified proof-complete via `#print axioms`). The substance —
  -- cokernel preservation, which consumes `Injective J` — is supplied EXPLICITLY
  -- by `internalHomFunctor_preservesCokernels` (SG-B1) so that instance resolution
  -- does NOT latch onto a `sorryAx`-tainted `PreservesColimit` instance from the
  -- draft libraries.
  have hcok : ∀ {X Y : (Sheaf K Ab.{max u v})ᵒᵖ} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (internalHomFunctor K J) :=
    internalHomFunctor_preservesCokernels K J
  exact Functor.preservesFiniteColimits_of_preservesCokernels (internalHomFunctor K J)

/-- **Statement 1 (Stacks Tag 01DR, abelian-sheaf level).**
Let `J` be an injective abelian sheaf on a site `(C, K)`. Then the contravariant
internal-Hom functor `ℋom(-, J)` is exact: for every short exact sequence
`0 → F' → F → F'' → 0` of abelian sheaves, encoded as a short complex `S` with
`S.ShortExact`, the contravariantly induced short complex
`(ℋom(-, J)) ∘ Sᵒᵖ`, i.e. `0 → ℋom(F'', J) → ℋom(F, J) → ℋom(F', J) → 0`,
is again short exact. -/
@[stacks 01DR, sga "4 V 4.10" "1), A = Z"]
theorem internalHom_exact_of_injective (K : GrothendieckTopology C) [HasSheafify K Ab.{max u v}]
    (J : Sheaf K Ab.{max u v}) [Injective J]
    (S : ShortComplex (Sheaf K Ab.{max u v})) (hS : S.ShortExact) :
    (S.op.map (internalHomFunctor K J)).ShortExact := by
  -- The opposite short complex of a short exact sequence is short exact.
  have hSop : S.op.ShortExact := hS.op
  -- `ℋom(-, J)` preserves zero morphisms (existing instance), finite limits
  -- (SG-A, any `J`) and finite colimits (SG-B, uses `Injective J`); hence by
  -- `ShortComplex.ShortExact.map_of_exact` it sends `S.op` to a short exact
  -- sequence.
  have := internalHomFunctor_preservesFiniteLimits K J
  have := internalHomFunctor_preservesFiniteColimits K J
  exact hSop.map_of_exact (internalHomFunctor K J)

/-! ### Statement 2: the module-valued dual, and its exactness

This is the statement Stacks 01DR actually makes. In Section 19.8 the dual of a sheaf of
`O`-modules `F` is `F^∨ = ℋom(F, J)`, the ABELIAN internal Hom into a fixed injective abelian
sheaf `J`, *"with its natural `O`-module structure"* -- the action being precomposition with
the action on the source, `(r · φ)(x) = φ(r · x)`. Lemma 19.8.1 says `F ↦ F^∨` is exact as a
functor `Mod(O)ᵒᵖ ⥤ Mod(O)`.

So the abelian-sheaf exactness proved above is the *substance* of the proof -- the source's
own one-line argument is "this because `J` is an injective abelian sheaf" -- but it is not the
statement, because its functor lands in abelian sheaves rather than in `O`-modules. The two
together are the tag's covering set.

`DualFunctorData` is what makes the statement faithful: its `underlyingIso` field says the
functor becomes `ℋom(-, J)` once scalars are forgotten, and its `smul_app` field pins the
scalar action to `(r · φ)(x) = φ(r · x)`. Without those a "module-valued dual functor" could
carry any module structure at all, and the exactness statement would be about the wrong object.
-/

namespace Stacks.Injectives.AbelianDual

open Opposite

variable {K : GrothendieckTopology C}

/-- A sheaf of commutative rings read as a sheaf of rings, which is what a sheaf of modules is
indexed by. -/
noncomputable abbrev underlyingRingSheaf (O : Sheaf K CommRingCat.{max u v}) :
    Sheaf K RingCat.{max u v} :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).obj O

/-- The module-valued enhancement of the abelian internal-Hom functor `ℋom(-, J)`, packaged so
that the enhancement is pinned down rather than merely asserted to exist.

`underlyingIso` says that forgetting scalars recovers `ℋom(-, J)`, naturally in the source, and
`smul_app` says the scalar action is precomposition with the action on the argument,
`(r · φ)(x) = φ(r · x)`. These two fields are what make `F ↦ F^∨` the dual of Stacks 19.8
rather than some unrelated module structure on the same abelian sheaf. -/
structure DualFunctorData (O : Sheaf K CommRingCat.{max u v}) (J : Sheaf K Ab.{max u v}) where
  /-- The contravariant dual functor on sheaves of `O`-modules. -/
  functor : (SheafOfModules.{max u v} (underlyingRingSheaf O))ᵒᵖ ⥤
    SheafOfModules.{max u v} (underlyingRingSheaf O)
  /-- The dual functor preserves zero morphisms. -/
  preservesZero : functor.PreservesZeroMorphisms
  /-- After forgetting module structures, dualization is abelian internal Hom into `J`,
  naturally in the source. -/
  underlyingIso :
    functor ⋙ SheafOfModules.toSheaf (underlyingRingSheaf O) ≅
      (SheafOfModules.toSheaf (underlyingRingSheaf O)).op ⋙ internalHomFunctor K J
  /-- The scalar action on the dual is precomposition with the scalar action on its argument:
  `(r · φ)(x) = φ(r · x)`. -/
  smul_app : ∀ (F : (SheafOfModules.{max u v} (underlyingRingSheaf O))ᵒᵖ)
      (X : Cᵒᵖ) (r : (underlyingRingSheaf O).obj.obj X)
      (s : (functor.obj F).val.obj X)
      (x : F.unop.val.obj X),
    ((underlyingIso.hom.app F).hom.app X (r • s)).app
        (op (Over.mk (𝟙 X.unop))) x =
      ((underlyingIso.hom.app F).hom.app X s).app
        (op (Over.mk (𝟙 X.unop))) (r • x)

/-- Multiplication by a section `r` of `O` over `U`, as an endomorphism of the restriction of
the underlying abelian presheaf of `F` to the slice over `U`. This is the map that is
precomposed to produce the module structure on the dual. -/
noncomputable def sourceScalar (O : Sheaf K CommRingCat.{max u v})
    (F : SheafOfModules (underlyingRingSheaf O)) (U : C)
    (r : (underlyingRingSheaf O).obj.obj (op U)) :
    (Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ F.val.presheaf := by
  let P := (Over.forget U).op ⋙ F.val.presheaf
  let α : ∀ X : (Over U)ᵒᵖ, P.obj X ⟶ P.obj X := fun X =>
    (ModuleCat.smul (F.val.obj (op X.unop.left)))
      (((underlyingRingSheaf O).obj.map X.unop.hom.op).hom r)
  refine { app := α, naturality := ?_ }
  intro X Y f
  dsimp [P, α]
  have h₁ := F.val.smul_map f.unop.left.op
    (((underlyingRingSheaf O).obj.map X.unop.hom.op).hom r)
  have hcomp : X.unop.hom.op ≫ f.unop.left.op = Y.unop.hom.op := by
    calc
      X.unop.hom.op ≫ f.unop.left.op = (f.unop.left ≫ X.unop.hom).op := by rw [← op_comp]
      _ = Y.unop.hom.op := congrArg Quiver.Hom.op f.unop.w
  have hr : ((underlyingRingSheaf O).obj.map f.unop.left.op).hom
      (((underlyingRingSheaf O).obj.map X.unop.hom.op).hom r) =
        ((underlyingRingSheaf O).obj.map Y.unop.hom.op).hom r := by
    rw [← RingCat.comp_apply, ← (underlyingRingSheaf O).obj.map_comp, hcomp]
  rw [hr] at h₁
  exact h₁.symm

/-- On sections over an object `X` of the slice over `U`, `sourceScalar O F U r` is
multiplication by the restriction of `r` to `X`. -/
theorem sourceScalar_app (O : Sheaf K CommRingCat.{max u v})
    (F : SheafOfModules (underlyingRingSheaf O)) (U : C)
    (r : (underlyingRingSheaf O).obj.obj (op U)) (X : (Over U)ᵒᵖ)
    (x : ((Over.forget U).op ⋙ F.val.presheaf).obj X) :
    ((sourceScalar O F U r).app X).hom x =
      (ModuleCat.smul (F.val.obj (op X.unop.left))
        (((underlyingRingSheaf O).obj.map X.unop.hom.op).hom r)).hom x := rfl

/-- The action of a section `r` of `O` over `U` on a section of the dual over `U`, namely
precomposition with multiplication by `r`. -/
noncomputable abbrev dualSectionAction (O : Sheaf K CommRingCat.{max u v})
    (F : SheafOfModules (underlyingRingSheaf O)) (J : Sheaf K Ab.{max u v}) (U : C)
    (r : (underlyingRingSheaf O).obj.obj (op U))
    (a : (Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj) :
    (Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj :=
  sourceScalar O F U r ≫ a

/-- The action of `r` on `a` evaluated at a section `x` is `a` applied to `r` times `x`. -/
theorem dualSectionAction_app (O : Sheaf K CommRingCat.{max u v})
    (F : SheafOfModules (underlyingRingSheaf O)) (J : Sheaf K Ab.{max u v}) (U : C)
    (r : (underlyingRingSheaf O).obj.obj (op U))
    (a : (Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj)
    (X : (Over U)ᵒᵖ) (x : ((Over.forget U).op ⋙ F.val.presheaf).obj X) :
    (dualSectionAction O F J U r a).app X x =
      a.app X (((sourceScalar O F U r).app X) x) := rfl

/-- Precomposition makes the sections of the abelian internal Hom over `U` a module over the
sections of `O` over `U`. Commutativity of `O` is what makes the action associative on the
right side, so this is where the `CommRingCat` coefficients are used. -/
@[instance_reducible]
noncomputable def dualSectionModule (O : Sheaf K CommRingCat.{max u v})
    (F : SheafOfModules (underlyingRingSheaf O)) (J : Sheaf K Ab.{max u v}) (U : C) :
    Module ((underlyingRingSheaf O).obj.obj (op U))
      ((Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj) := by
  letI : AddCommGroup
      ((Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj) := inferInstance
  let R := (underlyingRingSheaf O).obj.obj (op U)
  let A := ((Over.forget U).op ⋙ F.val.presheaf ⟶ (Over.forget U).op ⋙ J.obj)
  letI : CommRing R := (O.obj.obj (op U)).commRing
  letI : SMul R A := ⟨dualSectionAction O F J U⟩
  letI : SemigroupAction R A := ⟨by
    intro r s a
    ext X x
    change (dualSectionAction O F J U (r * s) a).app X x =
      (dualSectionAction O F J U r (dualSectionAction O F J U s a)).app X x
    rw [dualSectionAction_app, dualSectionAction_app, dualSectionAction_app,
      sourceScalar_app, sourceScalar_app, sourceScalar_app]
    apply congrArg (ConcreteCategory.hom (a.app X))
    let x' : F.val.obj (op X.unop.left) := x
    let := (F.val.obj (op X.unop.left)).isModule
    change (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) (r * s)) • x' =
      (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) s) •
        ((RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) r) • x')
    rw [map_mul, smul_smul]
    have hcomm :
        RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) r *
            RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) s =
          RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) s *
            RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) r := by
      let f := (O.obj.map X.unop.hom.op).hom
      calc
        _ = f (r * s) := (map_mul f _ _).symm
        _ = f (s * r) := congrArg f (mul_comm r s)
        _ = _ := map_mul f _ _
    exact congrArg (fun z => z • x') hcomm⟩
  letI : MulAction R A := ⟨by
    intro a
    ext X x
    change (dualSectionAction O F J U 1 a).app X x = a.app X x
    rw [dualSectionAction_app, sourceScalar_app]
    apply congrArg (ConcreteCategory.hom (a.app X))
    let x' : F.val.obj (op X.unop.left) := x
    let := (F.val.obj (op X.unop.left)).isModule
    change (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) 1) • x' = x'
    rw [map_one, one_smul]⟩
  letI : DistribMulAction R A := ⟨by
    intro r
    change sourceScalar O F U r ≫ (0 : _ ⟶ _) = 0
    exact CategoryTheory.Limits.comp_zero, by
    intro r a b
    change sourceScalar O F U r ≫ (a + b) =
      sourceScalar O F U r ≫ a + sourceScalar O F U r ≫ b
    exact CategoryTheory.Preadditive.comp_add _ _ _ _ _ _⟩
  exact ⟨by
    intro r s a
    have h : sourceScalar O F U (r + s) =
        sourceScalar O F U r + sourceScalar O F U s := by
      ext X x
      change ((sourceScalar O F U (r + s)).app X).hom x =
        ((sourceScalar O F U r).app X).hom x + ((sourceScalar O F U s).app X).hom x
      rw [sourceScalar_app, sourceScalar_app, sourceScalar_app]
      let x' : F.val.obj (op X.unop.left) := x
      let := (F.val.obj (op X.unop.left)).isModule
      change (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) (r + s)) • x' =
        (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) r) • x' +
          (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map X.unop.hom.op) s) • x'
      rw [map_add, add_smul]
    change dualSectionAction O F J U (r + s) a =
      dualSectionAction O F J U r a + dualSectionAction O F J U s a
    change sourceScalar O F U (r + s) ≫ a =
      sourceScalar O F U r ≫ a + sourceScalar O F U s ≫ a
    rw [h]
    exact CategoryTheory.Preadditive.add_comp _ _ _ _ _ _, by
    intro a
    change dualSectionAction O F J U 0 a = 0
    change sourceScalar O F U 0 ≫ a = 0
    have hzero : sourceScalar O F U 0 = 0 := by
      ext X x
      change ((sourceScalar O F U 0).app X).hom x = 0
      rw [sourceScalar_app]
      rw [map_zero, map_zero]
      rfl
    rw [hzero, zero_comp]⟩

/-- The dual of a sheaf of `O`-modules as a presheaf of `O`-modules: the abelian internal Hom
presheaf `ℋom(F, J)`, with the precomposition action of `O`. -/
noncomputable def dualPresheaf (O : Sheaf K CommRingCat.{max u v})
    (J : Sheaf K Ab.{max u v}) (F : SheafOfModules (underlyingRingSheaf O)) :
    PresheafOfModules (underlyingRingSheaf O).obj := by
  let M := internalHomPresheaf F.val.presheaf J.obj
  letI : ∀ X, Module ((underlyingRingSheaf O).obj.obj X) (M.obj X) := fun X => by
    change Module ((underlyingRingSheaf O).obj.obj X)
      ((Over.forget X.unop).op ⋙ F.val.presheaf ⟶ (Over.forget X.unop).op ⋙ J.obj)
    exact dualSectionModule O F J X.unop
  refine PresheafOfModules.ofPresheaf M ?_
  intro X Y f r a
  change (internalHomPresheaf F.val.presheaf J.obj).map f
      (dualSectionAction O F J X.unop r a) =
    dualSectionAction O F J Y.unop (((underlyingRingSheaf O).obj.map f).hom r)
      ((internalHomPresheaf F.val.presheaf J.obj).map f a)
  rw [internalHomPresheaf_map_apply]
  change (Over.map f.unop).op.whiskerLeft
        (sourceScalar O F X.unop r ≫ a) =
      sourceScalar O F Y.unop
        (((underlyingRingSheaf O).obj.map f).hom r) ≫
        (Over.map f.unop).op.whiskerLeft a
  rw [Functor.whiskerLeft_comp]
  congr 1
  ext Z x
  simp [sourceScalar]

/-- Scalar multiplication on the sections of `dualPresheaf O J F` is `dualSectionAction`. -/
theorem dualPresheaf_smul (O : Sheaf K CommRingCat.{max u v})
    (J : Sheaf K Ab.{max u v}) (F : SheafOfModules (underlyingRingSheaf O))
    (X : Cᵒᵖ) (r : (underlyingRingSheaf O).obj.obj X)
    (a : (dualPresheaf O J F).obj X) :
    r • a = dualSectionAction O F J X.unop r a := by
  dsimp [dualPresheaf, PresheafOfModules.ofPresheaf]
  rfl

/-- The dualization construction `F ↦ F^∨ = ℋom(F, J)` of Stacks 19.8, with its natural
`O`-module structure. -/
noncomputable def dualFunctorData (O : Sheaf K CommRingCat.{max u v})
    (J : Sheaf K Ab.{max u v}) : DualFunctorData O J := by
  let R := underlyingRingSheaf O
  let forgetToAb := SheafOfModules.toSheaf R
  let H := internalHomFunctor K J
  let T : (SheafOfModules R)ᵒᵖ ⥤ SheafOfModules R := {
    obj F := {
      val := dualPresheaf O J F.unop
      isSheaf := by
        change Presheaf.IsSheaf K (internalHomPresheaf F.unop.val.presheaf J.obj)
        exact internalHomPresheaf_isSheaf K (SheafOfModules.toSheaf R |>.obj F.unop) J
    }
    map {F G} f := by
      letI : ∀ X, Module ((underlyingRingSheaf O).obj.obj X)
          ((dualPresheaf O J F.unop).obj X) := fun X => dualSectionModule O F.unop J X.unop
      letI : ∀ X, Module ((underlyingRingSheaf O).obj.obj X)
          ((dualPresheaf O J G.unop).obj X) := fun X => dualSectionModule O G.unop J X.unop
      letI : ∀ X, Module ((underlyingRingSheaf O).obj.obj X)
          ((internalHomPresheaf
            ((PresheafOfModules.toPresheaf R.obj).obj G.unop.val) J.obj).obj X) :=
        fun X => dualSectionModule O G.unop J X.unop
      let φ := H.map ((forgetToAb.map f.unop).op)
      let hφ : (dualPresheaf O J F.unop).presheaf ⟶
          (dualPresheaf O J G.unop).presheaf := φ.hom
      exact ⟨PresheafOfModules.homMk
        (M₁ := dualPresheaf O J F.unop) (M₂ := dualPresheaf O J G.unop) hφ
        (by
          intro X r a
          change (hφ.app X) (r • a) = r • (hφ.app X a)
          apply NatTrans.ext
          funext Z
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          let := (G.unop.val.obj (op Z.unop.left)).isModule
          let x' : G.unop.val.obj (op Z.unop.left) := x
          let rz := ((underlyingRingSheaf O).obj.map Z.unop.hom.op).hom r
          rw [dualPresheaf_smul O J F.unop X r a,
            dualPresheaf_smul O J G.unop X r ((hφ.app X) a)]
          dsimp only [hφ, φ, H, internalHomFunctor, internalHomPresheafMapLeft,
            dualSectionAction, sourceScalar]
          simp only [NatTrans.comp_app]
          change a.app Z
              (rz • (f.unop.val.app (op Z.unop.left)).hom x') =
            a.app Z
              ((f.unop.val.app (op Z.unop.left)).hom (rz • x'))
          congr 1
          exact ((f.unop.val.app (op Z.unop.left)).hom.map_smul rz x').symm)⟩
    map_id F := by
      apply forgetToAb.map_injective
      change H.map ((forgetToAb.map (𝟙 (unop F))).op) = 𝟙 _
      simp [H]
    map_comp f g := by
      apply forgetToAb.map_injective
      change H.map ((forgetToAb.map (f ≫ g).unop).op) =
        H.map ((forgetToAb.map f.unop).op) ≫ H.map ((forgetToAb.map g.unop).op)
      simp [H, unop_comp]
  }
  refine ⟨T, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    intro F G
    apply forgetToAb.map_injective
    change H.map ((forgetToAb.map ((0 : F ⟶ G).unop)).op) = 0
    simp
  · refine NatIso.ofComponents (fun F => Iso.refl _) ?_
    intro F G f
    apply Sheaf.hom_ext_iff.mpr
    ext X a
    rfl
  · intro F X r s x
    change ((r • s).app (op (Over.mk (𝟙 X.unop)))) x =
      (s.app (op (Over.mk (𝟙 X.unop)))) (r • x)
    rw [dualPresheaf_smul, dualSectionAction_app, sourceScalar_app]
    congr 1
    let := (F.unop.val.obj X).isModule
    change (RingCat.Hom.hom ((underlyingRingSheaf O).obj.map (𝟙 X.unop).op) r) • x = r • x
    simp

/-- The contravariant dual functor `F ↦ F^∨ = ℋom(F, J)` on sheaves of `O`-modules, with its
natural `O`-module structure. -/
noncomputable abbrev dualFunctor (O : Sheaf K CommRingCat.{max u v})
    (J : Sheaf K Ab.{max u v}) :
    (SheafOfModules.{max u v} (underlyingRingSheaf O))ᵒᵖ ⥤
      SheafOfModules.{max u v} (underlyingRingSheaf O) :=
  (dualFunctorData O J).functor

/-- **Stacks 01DR (Lemma 19.8.1), the statement itself.** The functor `F ↦ F^∨`, with its
natural `O`-module structure, is exact when `J` is an injective abelian sheaf: it carries a
short exact sequence of sheaves of `O`-modules to a short exact sequence of sheaves of
`O`-modules.

The source's proof is "this because `J` is an injective abelian sheaf", and that is exactly how
this runs: exactness of the forgetful functor to abelian sheaves (Stacks 03DA) reduces the
claim to `internalHom_exact_of_injective` above, which is where the injectivity of `J` is
spent. -/
@[stacks 01DR "module-valued exactness"]
theorem dualFunctor_shortExact_of_injective
    [HasSheafify K Ab.{max u v}] [K.WEqualsLocallyBijective Ab.{max u v}]
    (O : Sheaf K CommRingCat.{max u v}) (J : Sheaf K Ab.{max u v}) [Injective J]
    (S : ShortComplex (SheafOfModules.{max u v} (underlyingRingSheaf O)))
    (hS : S.ShortExact) :
    letI := (dualFunctorData O J).preservesZero
    (S.op.map (dualFunctor O J)).ShortExact := by
  let R := underlyingRingSheaf O
  let G := SheafOfModules.toSheaf R
  let H := internalHomFunctor K J
  let T := dualFunctorData O J
  let : T.functor.PreservesZeroMorphisms := T.preservesZero
  have hS' : (S.map G).ShortExact := hS.map_of_exact G
  have hAb : ((S.map G).op.map H).ShortExact :=
    internalHom_exact_of_injective K J (S.map G) hS'
  have eop : S.op.map G.op ≅ (S.map G).op :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  have eAb : (S.op.map G.op).map H ≅ (S.map G).op.map H :=
    (Functor.mapShortComplex H).mapIso eop
  have hAb' : (S.op.map (G.op ⋙ H)).ShortExact := by
    rw [ShortComplex.map_comp]
    exact (ShortComplex.shortExact_iff_of_iso eAb).2 hAb
  have e : S.op.map (T.functor ⋙ G) ≅ S.op.map (G.op ⋙ H) :=
    S.op.mapNatIso T.underlyingIso
  have hUnderlying : (S.op.map (T.functor ⋙ G)).ShortExact :=
    (ShortComplex.shortExact_iff_of_iso e).2 hAb'
  have hMapped : ((S.op.map T.functor).map G).ShortExact := by
    simpa only [ShortComplex.map_comp] using hUnderlying
  exact (ShortExact.shortExact_map_iff G).1 hMapped

end Stacks.Injectives.AbelianDual

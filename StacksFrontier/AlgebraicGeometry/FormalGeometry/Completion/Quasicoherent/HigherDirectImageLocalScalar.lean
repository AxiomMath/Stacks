module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# A higher direct image multiplies by a function on an open of the base

Let `f : X ⟶ Y` be a morphism of schemes, `V ⊆ Y` an open and `U = f⁻¹(V)`. A function
`ρ ∈ Γ(Y, V)` is not a global function on `X`, so multiplication by it is not an endomorphism of
a sheaf of `𝒪_X`-modules and `R ᵖ f_*` cannot be applied to it. It *is* an endomorphism of a
sheaf of the shape `(j_U)_*𝒢`, whose sections over `W` are the sections of `𝒢` over
`U ∩ W` — a module over `Γ(X, U)`, where the inverse image of `ρ` lives. This file proves that
`R ᵖ f_*` carries that endomorphism to multiplication by `ρ` on sections over `V`:

`Γ(V, R ᵖ f_*((j_U)_*(ρ · 𝟙))) = ρ · 𝟙`.

This is the one input that the positive-degree graded-module structure of the setup paragraph of
[Stacks, Tag 02O7] needs and that functoriality of `R ᵖ f_*` alone does not supply: the action
of `⨁ₙ ℐⁿ` on `⨁ₙ R ᵖ f_*(ℐⁿℱ)` must be `𝒪_Y`-linear *in the algebra variable*, and a section
of `ℐⁱ` over `V` can be scaled by a function on `V` only.

## Main results

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.pushforward_linear`: the direct image along a
  morphism of schemes is linear over any ring mapping to the global functions on the target, the
  source being linear over that ring through the pullback of functions. This is
  `AlgebraicGeometry.over_pushforward_linear` without the detour through `Spec`: the linear
  structure used here is `AlgebraicGeometry.Scheme.linearOfRingHom`, which asks for a ring map
  into `Γ(X, ⊤)` and not for a morphism to a spectrum.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictIso`: the composite
  `𝒢 ↦ (R ᵖ f_*((j_U)_*𝒢))|_V` **is** `R ᵖ (f ∣_ V)_*`. The counit of
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` cancels `(j_U)_*` against restriction to
  `U`, and [Stacks, Tag 01E5] in the form `higherDirectImageRestrictIso` does the rest.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrict_linear`: that composite is
  therefore `Γ(Y, V)`-linear.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerived_map_pushforward_smul_app`:
  **the statement above**, on sections over `V`.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.morphismRestrict_appTop_comp_map` and
  `…appTop_topIso_inv_restrict`: the two routes from `Γ(Y, V)` to the sections of `𝒪_X` over the
  image in `X` of an open of `f⁻¹(V)` agree, both being `f.appLE`. This is what identifies the
  scalar that the conclusion above produces, which lives on the `V`-side, with the scalar the
  multiplication of the Rees algebra uses, which lives on the `X`-side.

## Implementation notes

The linear structures are `Scheme.linearOfRingHom`, hence `def`s introduced by `letI`: the ring
is not determined by the scheme. The ring is `Γ(V, 𝒪_V)`, which is `Γ(Y, V)` only up to the
identification `AlgebraicGeometry.Scheme.Opens.topIso`, and that identification is what turns the
scalar of the conclusion from a function on the scheme `V` into a function on the open `V ⊆ Y`.

The degrees are the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, because the two inputs are:
`CategoryTheory.Functor.linear_rightDerived`, which is about `rightDerived`, and
`higherDirectImageRestrictIso`, which is a natural isomorphism only in that indexing (the
`ℤ`-indexed `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` is
objectwise, so it cannot be whiskered).

The passage from sections over the top open of the scheme `V` to sections over the open `V ⊆ Y`
is the only place where the equality `V.ι ''ᵁ ⊤ = V` of opens intervenes. It is handled by
proving the conclusion for every open `W` of `Y` *together with* an equality
`V.ι ''ᵁ ⊤ = W`, which is a predicate in `W` alone, so that the transport is a rewrite and no
`eqToHom` survives into the statement.

## References

* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.SchemeHigherDirectImage

variable {X Y : Scheme.{u}}

/-! ### Linearity over a ring of functions -/

/-- `AlgebraicGeometry.Scheme.linearOfRingHom` read at `X.Modules`, which has its own category
instance and so is not reached by instance search from the one on sheaves of modules over the
structure sheaf. -/
@[instance_reducible]
public def linearModules (X : Scheme.{u}) (A : Type u) [Ring A] (φ : A →+* Γ(X, ⊤)) :
    Linear A X.Modules :=
  Scheme.linearOfRingHom.{u, u} X A φ

/-- A scalar acts on the sections of a morphism of `𝒪_X`-modules by the restriction of its
image under the structure map. -/
public theorem smul_app (A : Type u) [Ring A] (φ : A →+* Γ(X, ⊤))
    {M N : X.Modules} (a : A) (h : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    letI := linearModules X A φ
    (a • h).app U x = X.presheaf.map (homOfLE (le_top (a := U))).op (φ a) • h.app U x := by
  refine (Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ isTerminalTop φ a h (op U) x).trans
    ?_
  congr 2

/-- Pulling back global functions and restricting to an open `W` is `Scheme.Hom.appLE` from `⊤`. -/
private theorem appTop_comp_map_eq_appLE (g : X ⟶ Y) (W : X.Opens) :
    g.appTop ≫ X.presheaf.map (homOfLE (le_top (a := W))).op =
      g.appLE ⊤ W (le_top.trans (le_of_eq g.preimage_top.symm)) := rfl

/-- **The direct image along a morphism of schemes is linear over any ring of functions on the
target.** The scalar reaches the sections over an open `W` of the target by restriction from the
top open, and the sections of the source over `g⁻¹(W)` by the pullback of functions; the two
routes agree because both are `g.appLE ⊤ (g⁻¹(W))`. -/
public theorem pushforward_linear (g : X ⟶ Y) (A : Type u) [CommRing A] (φ : A →+* Γ(Y, ⊤)) :
    letI := linearModules Y A φ
    letI := linearModules X A ((g.appTop).hom.comp φ)
    (Scheme.Modules.pushforward g).Linear A := by
  let := linearModules Y A φ
  let := linearModules X A ((g.appTop).hom.comp φ)
  rw [Functor.linear_iff]
  intro M r
  ext W x
  have hL : ((Scheme.Modules.pushforward g).map (r • 𝟙 M)).app W x =
      X.presheaf.map (homOfLE (le_top (a := g ⁻¹ᵁ W))).op
        ((g.appTop).hom (φ r)) • (show Γ(M, g ⁻¹ᵁ W) from x) :=
    smul_app A ((g.appTop).hom.comp φ) r (𝟙 M) (g ⁻¹ᵁ W) x
  have hR : ((r • 𝟙 ((Scheme.Modules.pushforward g).obj M)).app W) x =
      (g.app W).hom (Y.presheaf.map (homOfLE (le_top (a := W))).op (φ r)) •
        (show Γ(M, g ⁻¹ᵁ W) from x) :=
    smul_app A φ r (𝟙 _) W x
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  have h2 : Y.presheaf.map (homOfLE (le_top (a := W))).op ≫ g.app W =
      g.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans (le_of_eq (g.preimage_top).symm)) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  exact congrArg (fun q : CommRingCat.Hom _ _ => q.hom (φ r))
    ((appTop_comp_map_eq_appLE g _).trans h2.symm)

/-! ### `R ᵖ f_*` of an extension from `f⁻¹(V)`, restricted to `V` -/

/-- **`𝒢 ↦ (R ᵖ f_*((j_{f⁻¹V})_*𝒢))|_V` is `R ᵖ (f ∣_ V)_*`.** The counit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` cancels the extension `(j_{f⁻¹V})_*`
against the restriction to `f⁻¹(V)` that [Stacks, Tag 01E5] produces, so no composition law for
derived functors is involved. -/
public def extendRestrictIso (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ≅
      Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι ⋙
        ((Scheme.Modules.pushforward f).rightDerived p ⋙
          Scheme.Modules.restrictFunctor V.ι) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorAdjCounitIso (f ⁻¹ᵁ V).ι).symm
      ((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (higherDirectImageRestrictIso f V p)

/-- The `Γ(V, 𝒪_V)`-linear structure on the modules over the open subscheme `V`. -/
public abbrev linearOnOpen (V : Y.Opens) : Linear ↥Γ(V.toScheme, ⊤) V.toScheme.Modules :=
  linearModules V.toScheme ↥Γ(V.toScheme, ⊤) (RingHom.id _)

/-- The `Γ(V, 𝒪_V)`-linear structure on the modules over `f⁻¹(V)`, the scalars acting through
the inverse image of functions along `f ∣_ V`. -/
public abbrev linearOnPreimage (f : X ⟶ Y) (V : Y.Opens) :
    Linear ↥Γ(V.toScheme, ⊤) (f ⁻¹ᵁ V).toScheme.Modules :=
  linearModules (f ⁻¹ᵁ V).toScheme ↥Γ(V.toScheme, ⊤)
    (((f ∣_ V).appTop).hom.comp (RingHom.id _))

/-- The higher direct images along `f ∣_ V` are `Γ(V, 𝒪_V)`-linear: the undirected pushforward
is, by `pushforward_linear`, and a right derived functor of a linear functor is linear. -/
public theorem rightDerived_morphismRestrict_linear (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    letI := linearOnOpen V
    letI := linearOnPreimage f V
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).Linear ↥Γ(V.toScheme, ⊤) := by
  let := linearOnOpen V
  let := linearOnPreimage f V
  have := pushforward_linear (f ∣_ V) ↥Γ(V.toScheme, ⊤) (RingHom.id _)
  infer_instance

/-- **`𝒢 ↦ (R ᵖ f_*((j_{f⁻¹V})_*𝒢))|_V` is `Γ(V, 𝒪_V)`-linear**, being isomorphic to
`R ᵖ (f ∣_ V)_*`. -/
public theorem extendRestrict_linear (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    letI := linearOnOpen V
    letI := linearOnPreimage f V
    (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι ⋙
      ((Scheme.Modules.pushforward f).rightDerived p ⋙
        Scheme.Modules.restrictFunctor V.ι)).Linear ↥Γ(V.toScheme, ⊤) := by
  let := linearOnOpen V
  let := linearOnPreimage f V
  have := rightDerived_morphismRestrict_linear f V p
  exact Functor.linear_of_iso ↥Γ(V.toScheme, ⊤) (extendRestrictIso f V p)

/-- **A higher direct image multiplies by a function on an open of the base.** For `ρ` a function
on `V` and `𝒢` a sheaf of modules on `f⁻¹(V)`, the `p`-th higher direct image of multiplication
by the inverse image of `ρ` on the extension `(j_{f⁻¹V})_*𝒢` acts on sections over `V` as
multiplication by `ρ`.

This is the `𝒪_Y`-linearity in the algebra variable of the action of `⨁ₙ ℐⁿ` on
`⨁ₙ R ᵖ f_*(ℐⁿℱ)`: a section of `ℐⁱ` over `V` can be scaled only by a function on `V`, and the
map it induces is a morphism of sheaves on `X` only after the target is extended from
`f⁻¹(V)`. -/
public theorem rightDerived_map_pushforward_smul_app (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)
    (G : (f ⁻¹ᵁ V).toScheme.Modules) (ρ : Γ(V.toScheme, ⊤))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj G), V)) :
    letI := linearOnPreimage f V
    (((Scheme.Modules.pushforward f).rightDerived p).map
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map (ρ • 𝟙 G))).app V x =
      V.topIso.hom ρ • x := by
  let := linearOnOpen V
  let := linearOnPreimage f V
  have := extendRestrict_linear f V p
  set T := Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι ⋙
    ((Scheme.Modules.pushforward f).rightDerived p ⋙
      Scheme.Modules.restrictFunctor V.ι) with hT
  have key : T.map (ρ • 𝟙 G) = ρ • 𝟙 (T.obj G) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  have main : ∀ (W : Y.Opens) (e : V.ι ''ᵁ ⊤ = W)
      (y : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj G), W)),
      (((Scheme.Modules.pushforward f).rightDerived p).map
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map (ρ • 𝟙 G))).app W y =
        Y.presheaf.map (eqToHom e.symm).op ρ • y := by
    rintro W rfl y
    have h0 := congrArg (fun ψ : T.obj G ⟶ T.obj G => ψ.app ⊤ y) key
    refine h0.trans ?_
    refine (smul_app ↥Γ(V.toScheme, ⊤) (RingHom.id _) ρ (𝟙 (T.obj G)) ⊤ y).trans ?_
    have hres := Scheme.Modules.smul_restrictAppIso_hom_apply (f := V.ι)
      (((Scheme.Modules.pushforward f).rightDerived p).obj
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj G)) ⊤
      (V.toScheme.presheaf.map (homOfLE (le_top (a := (⊤ : V.toScheme.Opens)))).op
        ((RingHom.id ↥Γ(V.toScheme, ⊤)) ρ)) y
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Modules.restrictAppIso] at hres
    refine hres.trans ?_
    congr 1
  exact main V (Scheme.Opens.ι_image_top V) x

/-! ### The inverse image of a function on `V`, read on `f⁻¹(V)` -/

/-- **The two routes from `Γ(Y, V)` to `Γ(X, (f⁻¹V).ι ''ᵁ W)` agree.** Transporting a function on
`V` to a global function on the scheme `V`, pulling it back along `f ∣_ V` and restricting to an
open `W` of `f⁻¹(V)` is the same as pulling it back along `f` and restricting to the image of `W`
in `X`: both are `AlgebraicGeometry.Scheme.Hom.appLE` of `f` between `V` and that image.

This is the scalar identity behind the `𝒪_Y`-linearity in the algebra variable of the action of
`⨁ₙ ℐⁿ` on `⨁ₙ R ᵖ f_*(ℐⁿℱ)`: the acting section is scaled on the `V`-side, where
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.linearOnPreimage` puts the scalars, while the
multiplication of the Rees algebra scales it on the `X`-side. -/
public theorem morphismRestrict_appTop_comp_map (f : X ⟶ Y) (V : Y.Opens)
    (W : (f ⁻¹ᵁ V).toScheme.Opens) :
    V.topIso.inv ≫ (f ∣_ V).appTop ≫
        (f ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE (le_top (a := W))).op =
      f.appLE V ((f ⁻¹ᵁ V).ι ''ᵁ W) ((f ⁻¹ᵁ V).ι_image_le W) := by
  have h2 := morphismRestrict_appLE f V ⊤ W
    (le_top.trans (le_of_eq ((f ∣_ V).preimage_top).symm))
  rw [appTop_comp_map_eq_appLE, h2, Scheme.Opens.topIso_inv]
  exact Scheme.Hom.map_appLE f _ _

/-- `morphismRestrict_appTop_comp_map` on a function. -/
public theorem appTop_topIso_inv_restrict (f : X ⟶ Y) (V : Y.Opens)
    (W : (f ⁻¹ᵁ V).toScheme.Opens) (ρ : Γ(Y, V)) :
    (f ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE (le_top (a := W))).op
        (((f ∣_ V).appTop) (V.topIso.inv ρ)) =
      X.presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι_image_le W)).op ((f.app V) ρ) :=
  congrArg (fun g : Γ(Y, V) ⟶ Γ((f ⁻¹ᵁ V).toScheme, W) => g ρ)
    (morphismRestrict_appTop_comp_map f V W)

end Stacks.AlgebraicGeometry.SchemeHigherDirectImage

end

end

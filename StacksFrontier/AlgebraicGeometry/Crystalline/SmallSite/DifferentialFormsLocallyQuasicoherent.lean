module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerPresheafModel
public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsLocallyQuasicoherent

/-!
# Local quasi-coherence of `Ω^i_{X/S}`

Fix a global crystalline situation `(p, (S, I, γ), X)` and let
`Ω^i_{X/S} = ⋀^i Ω_{X/S} = Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i` be the
presheaf of crystalline differential forms of degree `i` on the big crystalline category
`CRIS(X/S)`.  Over an object `(U, T, δ)` the restriction `(Ω^i_{X/S})_T` is the `𝒪_T`-module whose
sections over an open `W` of `T` are the sections of `Ω^i_{X/S}` over `(U ∩ W, W, δ|_W)`.  This
module proves that `(Ω^i_{X/S})_T` is a quasi-coherent `𝒪_T`-module for every object and every `i`,
which is the first clause of [Stacks, Tag 07KM] for the higher exterior powers.

For `Ω_{X/S}` itself that clause is
`Crystalline.GlobalCrystallineSituation.crysDifferentials_isLocallyQuasiCoherent`, and the general
case reduces to it: the restriction of `Ω^i_{X/S}` is the `i`-th sectionwise exterior power of
the restriction of `Ω_{X/S}`, that restriction has quasi-coherent associated sheaf
`...restrictedCrysDifferentialsSheaf`, and the exterior power of a quasi-coherent sheaf of modules
on a scheme is quasi-coherent (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower`).

The key step is that **a sectionwise exterior power is unchanged by restriction of scalars along an
isomorphism of presheaves of rings**, `PresheafOfModules.extPowRestrictScalarsIso`. It is needed
because the restriction of a presheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object
changes the scalars: the sections of `𝒪_{X/S}` over `(U ∩ W, W, δ|_W)` are the global sections of
the open subscheme `W`, which is the ring `Γ(W, 𝒪_T)` only through the isomorphism
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenRingHom`. So the exterior power
formed over `𝒪_{X/S}` and then restricted, and the exterior power of the restriction formed over
`𝒪_T`, are two different exterior powers of the same module over two spellings of the same ring,
and identifying them is exactly a base change of an exterior algebra along a ring isomorphism.

## Main definitions

* `PresheafOfModules.extPowRestrictScalarsEquiv` — the identification on sections over one object:
  the two exterior powers are compared by `ExteriorAlgebra.powMapₛₗ` in both directions.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysFormsPresheaf` — the `i`-th sectionwise
  exterior power over `𝒪_T` of the restriction of `Ω_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialForms` — the restriction of
  `Ω^i_{X/S}` itself to the ambient scheme of an object, at the spelling
  `...restrictedCrysDifferentials` uses for `Ω_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsSheaf` — the `𝒪_T`-module
  `(Ω^i_{X/S})_T`: the sheaf of `𝒪_T`-modules associated with that restriction.
* `Crystalline.GlobalCrystallineSituation.crysDifferentialFormsRestrictionSheaf` — the same module
  with its scalars read in the restriction of `𝒪_{X/S}` to `T`, which is the spelling of
  `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent`.
* `Crystalline.GlobalCrystallineSituation.restrictOpenRingHomInv` — the inverse of
  `...Thickening.restrictOpenRingHom`, which `isIso_restrictOpenRingHom` shows is an isomorphism.

## Main results

* `PresheafOfModules.extPowRestrictScalarsIso` — **a sectionwise exterior power commutes with
  restriction of scalars along an isomorphism of presheaves of rings**:
  `⋀^n ((restrictScalars β).obj N) ≅ (restrictScalars β).obj (⋀^n N)` for `β` a morphism of
  presheaves of rings admitting a two-sided inverse `γ`.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsIso` — **the restriction
  of `Ω^i_{X/S}` to `T` is the `i`-th sectionwise exterior power over `𝒪_T` of the restriction of
  `Ω_{X/S}`.**
* `Crystalline.GlobalCrystallineSituation.restrictedCrysFormsSheafIso` — the `𝒪_T`-module
  associated with that sectionwise exterior power is the bundled exterior power
  `⋀^i (Ω_{X/S})_T`, which is [Stacks, Tag 01CG] for a presheaf model.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsSheaf_isQuasicoherent` and
  `..._isQuasicoherentOnSite` — `(Ω^i_{X/S})_T` is a quasi-coherent `𝒪_T`-module, in Mathlib's
  sense and in the sense of [Stacks, Tag 03DL(6)].
* `Crystalline.GlobalCrystallineSituation.crysDifferentialForms_isLocallyQuasiCoherent` —
  **[Stacks, Tag 07KM] clause (1) for `Ω^i_{X/S}`, for every `i` and every object of
  `CRIS(X/S)`.**

## Implementation notes

`Ω^i_{X/S}` is a presheaf of modules on `CRIS(X/S)` and not a sheaf, so the `𝒪_T`-module
`(Ω^i_{X/S})_T` of the source is rendered as the sheaf of `𝒪_T`-modules *associated with* the
restriction, exactly as in `...crysDifferentials_isLocallyQuasiCoherent` for `Ω_{X/S}`. No
hypothesis is carried: no affineness, no finiteness, no local freeness, and nothing about the
crystal condition.

`PresheafOfModules.extPowRestrictScalarsIso` takes the inverse of `β` as data, together with the
two pointwise round-trip identities, rather than an `IsIso` hypothesis. That is what the
application needs: the two presheaves of rings here are `𝒪_T` and the restriction of `𝒪_{X/S}`,
spelled `A.restrictOpenFunctor.op ⋙ structureRingCatPresheaf S`, and the composite functor is
associated the other way than the lemma's `O₂ ⋙ forget₂ CommRingCat RingCat`. The two spellings are
definitionally equal, so passing a *term* across them is free, but instance search does not see
through the reassociation: elaborating `inv (Thickening.restrictOpenRingHom A)` at the lemma's
spelling of its type fails to find `IsIso (Thickening.restrictOpenRingHom A)`.
`restrictOpenRingHomInv` names that inverse once at the original spelling, after which the lemma
takes it as an ordinary argument.

The component isomorphism is built from `ExteriorAlgebra.powMapₛₗ` at the identity map of the
sections, which is semilinear over `β` because the restricted action *is* the original action read
through `β`; the three equations needed — the two round trips and the naturality square — are all
instances of `ExteriorAlgebra.mapₛₗ_eq_comp` and `ExteriorAlgebra.mapₛₗ_eq_self`, which say that a
base change along a composite is the composite of the base changes and that a base change along the
identity is the identity. Both sides of the naturality square are rewritten to the *same* base
change, along the composite ring homomorphism `(𝒪_T → 𝒪_{X/S})` followed by a restriction map, so
no computation inside an exterior algebra is needed. The element arguments of those lemmas are left
to unification and the proofs are closed with `exact`: the sections of a sectionwise exterior power
are a `Submodule` coercion through `ModuleCat.of`, and writing the coercion out by hand does not
elaborate, while `exact` is defeq-tolerant.

`restrictedCrysFormsSheafIso` is `SheafOfModules.presheafModelExteriorPowerIso` at the presheaf
model `...restrictedCrysDifferentials`, whose sheafification is
`...restrictedCrysDifferentialsSheaf` by definition — so the isomorphism that lemma asks for
between the sheaf and the sheafification of its model is `Iso.refl`.

## References

* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe v u w

namespace PresheafOfModules

section ExtPowRestrictScalars

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}}
  (β : O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶ O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w})
  (γ : O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶ O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w})
  (N : PresheafOfModules.{w} (O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- **The identity map of the sections over an object, as a `β`-semilinear map from the restriction
of scalars of `N` along `β` to `N` itself.** It is semilinear and not linear because the two
modules have different rings of scalars; the restricted action of `r` is by definition the action
of `β r`, which is exactly the semilinearity condition. -/
def restrictScalarsSemilinearId (X : Cᵒᵖ) :
    ((restrictScalars β).obj N).obj X →ₛₗ[(β.app X).hom] N.obj X where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The identity map of the sections over an object, as a `γ`-semilinear map from `N` to the
restriction of scalars of `N` along `β`.**  This is the direction that uses `γ` to be a right
inverse of `β`: the restricted action of `γ s` is the action of `β (γ s)`, which has to be the
action of `s`. -/
def restrictScalarsSemilinearIdInv
    (hγβ : ∀ (X : Cᵒᵖ) (s : ↥((O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)),
      (β.app X).hom ((γ.app X).hom s) = s) (X : Cᵒᵖ) :
    N.obj X →ₛₗ[(γ.app X).hom] ((restrictScalars β).obj N).obj X where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' s x := (congrArg (fun t ↦ t • x) (hγβ X s)).symm

/-- **On the sections over one object, the `n`-th exterior power of a restriction of scalars along
an isomorphism of presheaves of rings is the restriction of scalars of the `n`-th exterior power.**

Both maps are `ExteriorAlgebra.powMapₛₗ` at the identity of the sections — the base change of an
exterior algebra along a ring homomorphism and a semilinear map — once along `β` and once along
`γ`, and the two round trips are base changes along the composites, which the hypotheses say are
the identity. -/
def extPowRestrictScalarsEquiv
    (hβγ : ∀ (X : Cᵒᵖ) (r : ↥((O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)),
      (γ.app X).hom ((β.app X).hom r) = r)
    (hγβ : ∀ (X : Cᵒᵖ) (s : ↥((O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)),
      (β.app X).hom ((γ.app X).hom s) = s)
    (n : ℕ) (X : Cᵒᵖ) :
    (extPow n ((restrictScalars β).obj N)).obj X ≃ₗ[↥((O₁ ⋙ forget₂ CommRingCat.{w}
        RingCat.{w}).obj X)] ((restrictScalars β).obj (extPow n N)).obj X where
  toFun x := ExteriorAlgebra.powMapₛₗ n (β.app X).hom (restrictScalarsSemilinearId β N X) x
  map_add' x y :=
    map_add (ExteriorAlgebra.powMapₛₗ n (β.app X).hom (restrictScalarsSemilinearId β N X)) x y
  map_smul' r x :=
    (ExteriorAlgebra.powMapₛₗ n (β.app X).hom (restrictScalarsSemilinearId β N X)).map_smul' r x
  invFun y :=
    ExteriorAlgebra.powMapₛₗ n (γ.app X).hom (restrictScalarsSemilinearIdInv β γ N hγβ X) y
  left_inv x := by
    refine Subtype.ext ?_
    exact (ExteriorAlgebra.mapₛₗ_eq_comp (χ := RingHom.id _) (restrictScalarsSemilinearId β N X)
          (restrictScalarsSemilinearIdInv β γ N hγβ X) LinearMap.id
          (fun r ↦ (hβγ X r).symm) (fun _ ↦ rfl) _).symm.trans
      (ExteriorAlgebra.mapₛₗ_eq_self LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl) _)
  right_inv y := by
    refine Subtype.ext ?_
    exact (ExteriorAlgebra.mapₛₗ_eq_comp (χ := RingHom.id _)
          (restrictScalarsSemilinearIdInv β γ N hγβ X) (restrictScalarsSemilinearId β N X)
          LinearMap.id (fun s ↦ (hγβ X s).symm) (fun _ ↦ rfl) _).symm.trans
      (ExteriorAlgebra.mapₛₗ_eq_self LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl) _)

/-- **A restriction map of `N`, read as a semilinear map out of the restriction of scalars along
`β`.**  Its ring homomorphism is the composite of `β` over the source with the restriction map of
the target presheaf of rings; this is the single base change that both sides of the naturality
square of `extPowRestrictScalarsIso` reduce to. -/
def restrictScalarsSemilinearRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((restrictScalars β).obj N).obj X →ₛₗ[((O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map
        f).hom.comp (β.app X).hom] N.obj Y where
  toFun x := N.map f x
  map_add' := map_add (N.map f).hom
  map_smul' r x := N.map_smul f ((β.app X).hom r) x

/-- **A sectionwise exterior power is unchanged by restriction of scalars along an isomorphism of
presheaves of rings.**

Let `β` be a morphism of presheaves of rings of the shape at which exterior powers of presheaves of
modules are formed, and let `γ` be a two-sided inverse of it, given pointwise. Then for every
presheaf of modules `N` over the target and every `n`, the `n`-th sectionwise exterior power of the
restriction of scalars of `N` is the restriction of scalars of the `n`-th sectionwise exterior
power of `N`.

Over one object this is `extPowRestrictScalarsEquiv`.  The naturality square says that the base
change along `β` over the target object composed with the restriction map taken over the source
ring agrees with the restriction map taken over the target ring composed with the base change along
`β` over the source object; both are the base change along one composite ring homomorphism and one
restriction map, by `ExteriorAlgebra.mapₛₗ_eq_comp`, and the two composites agree because `β` is
natural. -/
def extPowRestrictScalarsIso
    (hβγ : ∀ (X : Cᵒᵖ) (r : ↥((O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)),
      (γ.app X).hom ((β.app X).hom r) = r)
    (hγβ : ∀ (X : Cᵒᵖ) (s : ↥((O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)),
      (β.app X).hom ((γ.app X).hom s) = s)
    (n : ℕ) :
    extPow n ((restrictScalars β).obj N) ≅ (restrictScalars β).obj (extPow n N) :=
  PresheafOfModules.isoMk
    (fun X ↦ (extPowRestrictScalarsEquiv β γ N hβγ hγβ n X).toModuleIso) fun {X Y} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
      have hnat : ∀ r : ↥((O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X),
          ((O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map f).hom ((β.app X).hom r) =
            (β.app Y).hom (((O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map f).hom r) := by
        intro r
        have eq := RingHom.congr_fun (congrArg RingCat.Hom.hom (β.naturality f)) r
        dsimp at eq
        exact eq.symm
      exact (ExteriorAlgebra.mapₛₗ_eq_comp
            (((restrictScalars β).obj N).restrictₛₗ f) (restrictScalarsSemilinearId β N Y)
            (restrictScalarsSemilinearRestrict β N f) hnat (fun _ ↦ rfl) _).symm.trans
        (ExteriorAlgebra.mapₛₗ_eq_comp (restrictScalarsSemilinearId β N X) (N.restrictₛₗ f)
          (restrictScalarsSemilinearRestrict β N f) (fun _ ↦ rfl) (fun _ ↦ rfl) _)

end ExtPowRestrictScalars

end PresheafOfModules

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-! ### The exterior power of the restriction -/

/-- **The `i`-th sectionwise exterior power over `𝒪_T` of the restriction of `Ω_{X/S}` to the
ambient scheme of an object.**  Its sections over an open `W` of `T` are the `i`-th exterior power
over `Γ(W, 𝒪_T)` of the sections of `Ω_{X/S}` over `(U ∩ W, W, δ|_W)`.
`restrictedCrysDifferentialFormsIso` identifies it with the restriction of `Ω^i_{X/S}`. -/
def restrictedCrysFormsPresheaf (A : Thickening S) (i : ℕ) :
    A.thickening.target.scheme.PresheafOfModules :=
  PresheafOfModules.extPow i (restrictedCrysDifferentials S A)

/-- The sheaf of `𝒪_T`-modules associated with `restrictedCrysFormsPresheaf`. -/
def restrictedCrysFormsSheaf (A : Thickening S) (i : ℕ) :
    SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).obj
    (restrictedCrysFormsPresheaf S A i)

/-- **The sheaf associated with the `i`-th sectionwise exterior power of the restriction of
`Ω_{X/S}` is the `i`-th exterior power of the `𝒪_T`-module `(Ω_{X/S})_T`.**

This is [Stacks, Tag 01CG] in the presheaf-model form
`SheafOfModules.presheafModelExteriorPowerIso`: the exterior power of a sheaf of modules is the
sheafification of the sectionwise exterior power of any presheaf model of it, and the restriction
`...restrictedCrysDifferentials` is a presheaf model of `...restrictedCrysDifferentialsSheaf` by
the definition of the latter. -/
def restrictedCrysFormsSheafIso (A : Thickening S) (i : ℕ) :
    restrictedCrysFormsSheaf S A i ≅
      Scheme.Modules.exteriorPower (restrictedCrysDifferentialsSheaf S A) i :=
  SheafOfModules.presheafModelExteriorPowerIso _ (restrictedCrysDifferentials S A)
    (SheafOfModules.algebras _ (restrictedCrysDifferentialsSheaf S A)) (Iso.refl _) i

/-- **The sheaf associated with the `i`-th sectionwise exterior power of the restriction of
`Ω_{X/S}` is quasi-coherent.**  It is the `i`-th exterior power of `(Ω_{X/S})_T` by
`restrictedCrysFormsSheafIso`, that module is quasi-coherent by
`...restrictedCrysDifferentialsSheaf_isQuasicoherent` — which is [Stacks, Tag 07IZ] followed by
[Stacks, Tag 07IY] — and every exterior power of a quasi-coherent sheaf of modules on a scheme is
quasi-coherent. -/
instance restrictedCrysFormsSheaf_isQuasicoherent (A : Thickening S) (i : ℕ) :
    (restrictedCrysFormsSheaf S A i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent A.thickening.target.scheme.ringCatSheaf).prop_of_iso
    (restrictedCrysFormsSheafIso S A i).symm
    (Scheme.Modules.isQuasicoherent_exteriorPower (restrictedCrysDifferentialsSheaf S A) i)

/-! ### The restriction of the structure sheaf is an isomorphism -/

/-- **The identification of the sections of `𝒪_X` over an open with the global sections of the open
subscheme is an isomorphism**, its inverse being `Crystalline.openTopResInv`. -/
instance isIso_openTopRes {X : Scheme.{u}} (W : X.Opens) : IsIso (openTopRes W) :=
  ⟨openTopResInv W, openTopRes_openTopResInv W, openTopResInv_openTopRes W⟩

/-- Each component of `...Thickening.restrictOpenRingHom` is an isomorphism, being the image of
`Crystalline.openTopRes` under the forgetful functor to rings. -/
instance isIso_restrictOpenRingHom_app (A : Thickening S)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ) :
    IsIso ((Thickening.restrictOpenRingHom A).app W) :=
  inferInstanceAs (IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map (openTopRes W.unop)))

/-- **The comparison of `𝒪_T` with the restriction of the structure presheaf of `CRIS(X/S)` to the
opens of `T` is an isomorphism of presheaves of rings.** -/
instance isIso_restrictOpenRingHom (A : Thickening S) :
    IsIso (Thickening.restrictOpenRingHom A) :=
  NatIso.isIso_of_isIso_app _

/-- The inverse of `...Thickening.restrictOpenRingHom`: the morphism of presheaves of rings from
the restriction of the structure presheaf of `CRIS(X/S)` to the opens of `T` to `𝒪_T`. -/
def restrictOpenRingHomInv (A : Thickening S) :
    ((A.restrictOpenFunctor).op ⋙ structureRingCatPresheaf S) ⟶
      A.thickening.target.scheme.ringCatSheaf.obj :=
  inv (Thickening.restrictOpenRingHom A)

/-- `restrictOpenRingHomInv` is a left inverse on sections. -/
theorem restrictOpenRingHom_inv_app_app (A : Thickening S)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ)
    (r : ↥(A.thickening.target.scheme.ringCatSheaf.obj.obj W)) :
    ((restrictOpenRingHomInv S A).app W).hom
        (((Thickening.restrictOpenRingHom A).app W).hom r) = r :=
  RingHom.congr_fun (congrArg RingCat.Hom.hom
    (NatTrans.congr_app (IsIso.hom_inv_id (Thickening.restrictOpenRingHom A)) W)) r

/-- `restrictOpenRingHomInv` is a right inverse on sections. -/
theorem restrictOpenRingHom_app_inv_app (A : Thickening S)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ)
    (s : ↥(((A.restrictOpenFunctor).op ⋙ structureRingCatPresheaf S).obj W)) :
    ((Thickening.restrictOpenRingHom A).app W).hom
        (((restrictOpenRingHomInv S A).app W).hom s) = s :=
  RingHom.congr_fun (congrArg RingCat.Hom.hom
    (NatTrans.congr_app (IsIso.inv_hom_id (Thickening.restrictOpenRingHom A)) W)) s

/-! ### Clause (1) of Stacks 07KM for `Ω^i_{X/S}` -/

/-- **The restriction of `Ω^i_{X/S}` to the ambient scheme of an object of `CRIS(X/S)`.**  Its
sections over an open `W` of `T` are the sections of `Ω^i_{X/S}` over the restriction of
`(U, T, δ)` to `W`, viewed as a module over `Γ(W, 𝒪_T)`.  This is
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentials` with `Ω_{X/S}` replaced by
`Ω^i_{X/S}`. -/
def restrictedCrysDifferentialForms (A : Thickening S) (i : ℕ) :
    A.thickening.target.scheme.PresheafOfModules :=
  (PresheafOfModules.pushforward (Thickening.restrictOpenRingHom A)).obj
    (crysDifferentialForms S i)

/-- **The restriction of `Ω^i_{X/S}` to the ambient scheme of an object is the `i`-th sectionwise
exterior power over `𝒪_T` of the restriction of `Ω_{X/S}`.**

Restriction along the functor of restrictions of the object changes neither the sections nor the
transition maps, so it commutes with the sectionwise exterior power on the nose; what remains is
the change of scalars from the restriction of `𝒪_{X/S}` to `𝒪_T`, and an exterior power is
unchanged by a change of scalars along an isomorphism of presheaves of rings, which is
`PresheafOfModules.extPowRestrictScalarsIso`. The isomorphism used is
`...Thickening.restrictOpenRingHom`, invertible by `isIso_restrictOpenRingHom`. -/
def restrictedCrysDifferentialFormsIso (A : Thickening S) (i : ℕ) :
    restrictedCrysDifferentialForms S A i ≅ restrictedCrysFormsPresheaf S A i :=
  (PresheafOfModules.extPowRestrictScalarsIso
    (O₁ := A.thickening.target.scheme.presheaf)
    (O₂ := (A.restrictOpenFunctor).op ⋙ structureRingPresheaf S)
    (Thickening.restrictOpenRingHom A) (restrictOpenRingHomInv S A)
    ((PresheafOfModules.pushforward₀ A.restrictOpenFunctor (crisRing S)).obj
      (crysDifferentials S))
    (restrictOpenRingHom_inv_app_app S A) (restrictOpenRingHom_app_inv_app S A) i).symm

/-- **The `𝒪_T`-module `(Ω^i_{X/S})_T`.**  The sheaf of `𝒪_T`-modules associated with the
restriction of `Ω^i_{X/S}` to the ambient scheme `T` of an object `(U, T, δ)` of `CRIS(X/S)`; the
restriction itself is only a presheaf of modules, so the `𝒪_T`-module of the source is its
associated sheaf, as it is for `Ω_{X/S}` in
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheaf`. -/
def restrictedCrysDifferentialFormsSheaf (A : Thickening S) (i : ℕ) :
    SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).obj
    (restrictedCrysDifferentialForms S A i)

/-- **The `𝒪_T`-module `(Ω^i_{X/S})_T` is quasi-coherent.**  The restriction of `Ω^i_{X/S}` is the
`i`-th sectionwise exterior power of the restriction of `Ω_{X/S}`, by
`restrictedCrysDifferentialFormsIso`, and the sheaf associated with that is quasi-coherent by
`restrictedCrysFormsSheaf_isQuasicoherent`. -/
instance restrictedCrysDifferentialFormsSheaf_isQuasicoherent (A : Thickening S) (i : ℕ) :
    (restrictedCrysDifferentialFormsSheaf S A i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent A.thickening.target.scheme.ringCatSheaf).prop_of_iso
    ((PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).mapIso
      (restrictedCrysDifferentialFormsIso S A i).symm)
    (restrictedCrysFormsSheaf_isQuasicoherent S A i)

/-- **The `𝒪_T`-module `(Ω^i_{X/S})_T` is quasi-coherent in the sense of [Stacks, Tag 03DL(6)]**:
every open of `T` has a cover on whose members the module is a cokernel of a map between free
modules.  On the Zariski site of a scheme this is the same condition as Mathlib's. -/
theorem restrictedCrysDifferentialFormsSheaf_isQuasicoherentOnSite (A : Thickening S) (i : ℕ) :
    (restrictedCrysDifferentialFormsSheaf S A i).IsQuasicoherentOnSite :=
  SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent
    (restrictedCrysDifferentialFormsSheaf S A i)

/-- **The module `(Ω^i_{X/S})_T`, with its scalars read in the restriction of `𝒪_{X/S}`.** The same
module as `restrictedCrysDifferentialFormsSheaf`, over the restriction of the structure sheaf of
`CRIS(X/S)` to the opens of `T` instead of over `𝒪_T`; the two sheaves of rings are identified by
`...Thickening.ringRestrictionSheafStructureIso`, so this is a restriction of scalars along an
isomorphism and the sections are unchanged.  This is the spelling in which
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` asks for quasi-coherence, and the
one `...crysDifferentialsRestrictionSheaf` uses for `Ω_{X/S}`. -/
def crysDifferentialFormsRestrictionSheaf (A : Thickening S) (i : ℕ) :
    SheafOfModules.{u} A.ringRestrictionSheaf :=
  (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).hom).obj
    (restrictedCrysDifferentialFormsSheaf S A i)

/-- **Clause (1) of [Stacks, Tag 07KM] for `Ω^i_{X/S}`.**  For every `i : ℕ`, the presheaf
`Ω^i_{X/S} = ⋀^i Ω_{X/S}` of crystalline differential forms of degree `i` is locally
quasi-coherent: for every object `(U, T, δ)` of `CRIS(X/S)` the restriction `(Ω^i_{X/S})_T` is a
quasi-coherent module over the structure sheaf of the ambient scheme `T`, here read as the
restriction of `𝒪_{X/S}` to the opens of `T`.

The restriction of `Ω^i_{X/S}` is the `i`-th sectionwise exterior power of the restriction of
`Ω_{X/S}`, and the latter is `Ω_{T/S,δ}` by [Stacks, Tag 07IZ], quasi-coherent by
[Stacks, Tag 07IY]; exterior powers of a quasi-coherent module are quasi-coherent. The degree-one
case is `Crystalline.GlobalCrystallineSituation.crysDifferentials_isLocallyQuasiCoherent`, up to
the identification `Ω^1_{X/S} = Ω_{X/S}`, which is not used here: the exterior power is handled in
its own right, for every `i` including `i = 0` and `i = 1`.

The restriction is taken as a sheaf of modules, namely the sheaf associated with the restriction of
the presheaf `Ω^i_{X/S}`. -/
theorem crysDifferentialForms_isLocallyQuasiCoherent (A : Thickening S) (i : ℕ) :
    (crysDifferentialFormsRestrictionSheaf S A i).IsQuasicoherentOnSite :=
  Thickening.isQuasicoherentOnSite_ofAmbient A _
    (restrictedCrysDifferentialFormsSheaf_isQuasicoherentOnSite S A i)

end Crystalline.GlobalCrystallineSituation

end

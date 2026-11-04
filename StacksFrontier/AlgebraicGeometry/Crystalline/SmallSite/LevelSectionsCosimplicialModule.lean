module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.EnvelopeCosimplicialComparison

/-!
# The cosimplicial `D(*)`-module of sections at a fixed `p`-adic level

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, and let
`(X, T(n)_e, δ(n))` be the cosimplicial system of thickenings of [Stacks, Tag 07JN] which
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` constructs.  For a sheaf of
`𝒪_{X/S}`-modules `F` on the small crystalline site and a fixed `p`-adic level `e`, the groups

`L_n = Γ((X, T(n)_e, δ(n)), F)`

form a cosimplicial module over the cosimplicial ring `D(0) → D(1) → D(2) → ⋯` of
`...SmallSite.wholeSpaceEnvelopeRing`.  This file writes that cosimplicial module down.

The scalars are the whole content.  The sections of `F` over an object of `Cris(X/S)` are a module
over the sections of `𝒪_{X/S}` there — that is what a sheaf of `𝒪_{X/S}`-modules is — and
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` identifies the section ring of the level `(n, e)`
with the finite level `D(n)/(p)^{N + e}`.  Composing the quotient map `D(n) → D(n)/(p)^{N + e}`
with the inverse of that identification gives a ring map `D(n) → Γ(T(n)_e, 𝒪)`, which is
`levelSectionsScalars`, and restriction of scalars along it makes the sections a `D(n)`-module,
which is `levelSectionsModule`.  It is registered as an instance, so the transport is paid for
once and never re-derived inside a proof.

In the cosimplicial direction the transition map of `L_*` is the restriction map of `F` along the
transition `T(m)_e ⟶ T(n)_e` of the system.  It is not `D(n)`-linear — it cannot be, source and
target being modules over different rings — but it is semilinear along the structure map
`D(n) ⟶ D(m)` of `D(*)`, and that is exactly the cosimplicial naturality
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` of the level identification, read on the
scalars as `levelSectionsScalars_restriction`.  So the data assembles into a
`Crystalline.SemilinearCosimplicialModule` over `...SmallSite.wholeSpaceEnvelopeRing`, which is
`levelSectionsData`, and `Crystalline.SemilinearCosimplicialModule.toCosimplicialModule` turns
that into the `Crystalline.CosimplicialModule` `levelSectionsCosimplicialModule`.

That last object is the `L_*` which the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` quantifies over, and the computation
lemmas at the end of the file are what makes it usable: they identify the degreewise carrier and
the degreewise map of `L_*` with the sections of `F` and with the restriction maps of `F`, both
before and after the passage to cosimplicial abelian groups in which the isomorphism `ε` of
`hiso` lives.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalars` — the ring map
  `D(n) → Γ(T(n)_e, 𝒪)` through which the sections of a sheaf of `𝒪_{X/S}`-modules over the
  level `(n, e)` become a `D(n)`-module.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsModule` — that `D(n)`-module
  structure on the sections, as an instance.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsData` — the degreewise modules
  together with the restriction maps of `F`, as semilinear data over
  `...SmallSite.wholeSpaceEnvelopeRing`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsCosimplicialModule` — **the
  cosimplicial `D(*)`-module `L_*` of the sections of `F` at the `p`-adic level `e`.**

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalars_restriction` — the
  scalars are compatible with the cosimplicial direction: restricting `levelSectionsScalars` of a
  scalar along a transition map of the system gives `levelSectionsScalars` of its image under the
  structure map of `D(*)`.  This is the semilinearity of `L_*`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsCosimplicialModule_obj` and
  `...SmallSite.levelSectionsCosimplicialModule_map_apply` — the degreewise carrier of `L_*` is
  the group of sections of `F` over `(X, T(n)_e, δ(n))` and its degreewise map is the restriction
  map of `F`, both by `rfl`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsCosimplicialModule_forget_obj`
  and `...SmallSite.levelSectionsCosimplicialModule_forget_map_apply` — the same two
  identifications for the underlying cosimplicial abelian group of `L_*`.

## Implementation notes

Everything here is indexed by `SimplexCategory` rather than by `ℕ`, although the level
identification `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` it rests on is stated for `n : ℕ`.
The reason is instance resolution.  The `module` field of
`Crystalline.SemilinearCosimplicialModule` has to be found by typeclass synthesis at a bare
`SimplexCategory` variable `n` — the structure's later fields mention the module structure in
their types, so the construction only elaborates if `Module (D(n)) (L_n)` is synthesizable — and
the discrimination tree does not reach an instance whose index is written `⦋n⦌` from a goal whose
index is a variable of `SimplexCategory`.  So `levelSectionsModule` is stated over
`n : SimplexCategory`, and `n.len` appears only where the `ℕ`-indexed statements of
`SmallSite/EnvelopeCosimplicialComparison.lean` are applied.  Nothing is lost: `⦋n.len⦌` and `n`
are the same term by eta for structures, so the two spellings are interchangeable by `rfl`.

`Crystalline.SemilinearCosimplicialModule.toCosimplicialModule` requires the diagonal
`Crystalline.SemilinearCosimplicialModule.{u, u}`, since `Crystalline.CosimplicialModule` is a
`PresheafOfModules.{u}` over the presheaf of rings of the cosimplicial ring.  That is no
restriction here: `...SmallSite.wholeSpaceEnvelopeRing` is a cosimplicial object of
`CommRingCat.{u}` and the sections of `F : SheafOfModules.{u} (structureSheaf S)` are in
`Type u`.

`toCosimplicialModule` carries no `obj` or `map` simp lemmas, so the computation lemmas are
stated in the spelling a consumer has — the sections of `F` and the restriction maps of `F` — and
proved by `rfl`.  They are deliberately not stated at the level of `ModuleCat.of`: the ring of a
degree of a `Crystalline.CosimplicialModule` is spelled
`(cosimplicialRingPresheaf A).obj (op (op n))` while the module structure built here is indexed by
`A.obj n`, and although the two are definitionally equal, asking typeclass synthesis to bridge
them is the kind of identification that has to be paid for in a definition rather than inside
unification.

## What is and is not proved

**No tag attribute of any kind is placed in this file, and [Stacks, Tag 07LF] is not proved.**
What is constructed is one of the inputs of the remaining step of that tag: the cosimplicial
`D(*)`-module `L_*` of the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso`, together with the computation
lemmas needed to work with it.

**The isomorphism `ε` of `hiso` is not constructed here**, and nothing in this file asserts that
`L_* ⊗_{D(*)} Ω^i_{D(*)}` is isomorphic to `M(•)_e` for the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.  The sheaf `F` is an arbitrary sheaf of `𝒪_{X/S}`-modules: neither
hypothesis (1) nor hypothesis (2) of [Stacks, Tag 07JN] is used or assumed.

No hypothesis is carried beyond `hp`, the nilpotence of `p` on `Γ(X, ⊤)` which
`...SmallSite.wholeSpaceSystem` itself needs, and the two affineness instances `[IsAffine S.X]`
and `[IsAffine S.S.scheme]` which `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` carries.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07L9](https://stacks.math.columbia.edu/tag/07L9)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-! ### The scalars -/

/-- **The ring map `D(n) → Γ(T(n)_e, 𝒪)` through which the level `(n, e)` of the system of
[Stacks, Tag 07JN] is a `D(n)`-algebra**: the quotient map onto the finite level
`D(n)/(p)^{N + e}` followed by the inverse of the identification
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` of that finite level with the section ring of the
level.

It is not injective — the level is a quotient of `D(n)` — and that is the point: restriction of
scalars along it is what makes sections over the level into `D(n)`-modules. -/
def levelSectionsScalars (n : SimplexCategory) (e : ℕ) :
    ((wholeSpaceEnvelopeRing hp).obj n : Type u) →+*
      ((structureSheaf S).val.obj
        (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u) :=
  (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm.toRingHom.comp (Ideal.Quotient.mk _)

/-- `levelSectionsScalars` is the inverse of the level identification applied to the class of the
scalar modulo `(p)^{N + e}`. -/
theorem levelSectionsScalars_apply (n : SimplexCategory) (e : ℕ)
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u)) :
    levelSectionsScalars hp n e r =
      (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm (Ideal.Quotient.mk _ r) :=
  rfl

/-- **The sections of a sheaf of `𝒪_{X/S}`-modules over the level `(n, e)` of the system of
[Stacks, Tag 07JN] are a module over the degree `n` of `...SmallSite.wholeSpaceEnvelopeRing`.**

The sections are a module over the section ring of `𝒪_{X/S}` at that object, which is what
`F : SheafOfModules _ (structureSheaf S)` provides; restriction of scalars along
`levelSectionsScalars` carries that to `D(n)`.

This is an instance rather than a plain definition because the semilinear data of
`levelSectionsData` is only elaborated once this module structure is synthesizable, and because
the transport should be performed once here instead of being re-derived at each use. -/
instance levelSectionsModule (F : SheafOfModules.{u} (structureSheaf S)) (n : SimplexCategory)
    (e : ℕ) :
    Module ((wholeSpaceEnvelopeRing hp).obj n)
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  Module.compHom _ (levelSectionsScalars hp n e)

/-- A scalar of `D(n)` acts on a section over the level `(n, e)` through
`levelSectionsScalars`. -/
theorem levelSectionsModule_smul (F : SheafOfModules.{u} (structureSheaf S))
    (n : SimplexCategory) (e : ℕ)
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u))
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    r • x = levelSectionsScalars hp n e r • x :=
  rfl

/-- **The scalars of the levels are compatible with the cosimplicial direction.**  Restricting
`levelSectionsScalars hp n e r` along the transition map `T(m)_e ⟶ T(n)_e` of the system of
[Stacks, Tag 07JN] gives `levelSectionsScalars hp m e` of the image of `r` under the structure map
`D(n) ⟶ D(m)` of `...SmallSite.wholeSpaceEnvelopeRing`.

This is the cosimplicial naturality `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` of the
level identification, read on the scalars, and it is what makes the restriction maps of a sheaf
of `𝒪_{X/S}`-modules semilinear over `D(*)`. -/
theorem levelSectionsScalars_restriction {n m : SimplexCategory} (φ : n ⟶ m) (e : ℕ)
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u)) :
    ((structureSheaf S).val.map (((wholeSpaceSystem S hp).map φ.op).app e).op).hom
        (levelSectionsScalars hp n e r) =
      levelSectionsScalars hp m e (((wholeSpaceEnvelopeRing hp).map φ).hom r) := by
  refine (wholeSpaceEnvelopeRingLevelEquiv hp m.len e).injective ?_
  refine Eq.trans (wholeSpaceEnvelopeRingLevelEquiv_map hp (n := n.len) (m := m.len) φ e
    (levelSectionsScalars hp n e r)) ?_
  show Ideal.quotientMap _ _ _ (wholeSpaceEnvelopeRingLevelEquiv hp n.len e
      ((wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm (Ideal.Quotient.mk _ r))) =
    wholeSpaceEnvelopeRingLevelEquiv hp m.len e
      ((wholeSpaceEnvelopeRingLevelEquiv hp m.len e).symm
        (Ideal.Quotient.mk _ (((wholeSpaceEnvelopeRing hp).map φ).hom r)))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Ideal.quotientMap_mk]

/-! ### The cosimplicial module -/

variable (F : SheafOfModules.{u} (structureSheaf S)) (e : ℕ)

/-- **The sections of `F` over the levels `(n, e)` of the system of [Stacks, Tag 07JN], as
semilinear data over `...SmallSite.wholeSpaceEnvelopeRing`.**

In degree `n` the `D(n)`-module `Γ((X, T(n)_e, δ(n)), F)` of `levelSectionsModule`, with the
restriction map of `F` along the transition map `T(m)_e ⟶ T(n)_e` as the transition map; its
semilinearity over the structure map `D(n) ⟶ D(m)` is `levelSectionsScalars_restriction`.

The `p`-adic level `e` is fixed throughout: no limit over the levels is taken, which is what
distinguishes this from `...SmallSite.cosimplicialSections`. -/
def levelSectionsData : SemilinearCosimplicialModule.{u, u} (wholeSpaceEnvelopeRing hp) where
  obj n := (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u)
  addCommGroup _n := inferInstance
  module n := inferInstanceAs (Module ((wholeSpaceEnvelopeRing hp).obj n)
    (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))))
  map {n m} φ :=
    { toFun := fun x => F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op x
      map_add' := map_add _
      map_smul' := fun r x => by
        change F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op
            (levelSectionsScalars hp n e r • x) = _
        rw [PresheafOfModules.map_smul]
        exact congrArg (fun s => s • F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op x)
          (levelSectionsScalars_restriction hp φ e r) }
  map_id_apply n x := by
    refine Eq.trans (PresheafOfModules.congr_map_apply F.val
      (f := (((wholeSpaceSystem S hp).map (𝟙 n).op).app e).op)
      (g := 𝟙 (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) (by simp) x) ?_
    rw [F.val.map_id, ModuleCat.restrictScalarsId'_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply]
  map_comp_apply {n m l} φ ψ x := by
    refine Eq.trans (PresheafOfModules.congr_map_apply F.val
      (f := (((wholeSpaceSystem S hp).map (φ ≫ ψ).op).app e).op)
      (g := (((wholeSpaceSystem S hp).map φ.op).app e).op ≫
        (((wholeSpaceSystem S hp).map ψ.op).app e).op) (by simp) x) ?_
    exact PresheafOfModules.map_comp_apply _ _ _ _

/-- The degree `n` of `levelSectionsData` is the group of sections of `F` over
`(X, T(n)_e, δ(n))`. -/
theorem levelSectionsData_obj (n : SimplexCategory) :
    (levelSectionsData hp F e).obj n =
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u) :=
  rfl

/-- The transition map of `levelSectionsData` along `φ : ⦋n⦌ ⟶ ⦋m⦌` is the restriction map of `F`
along the transition map `T(m)_e ⟶ T(n)_e` of the system of [Stacks, Tag 07JN]. -/
theorem levelSectionsData_map_apply {n m : SimplexCategory} (φ : n ⟶ m)
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    (levelSectionsData hp F e).map φ x =
      F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op x :=
  rfl

/-- **The cosimplicial `D(*)`-module `L_*` of the sections of `F` at the `p`-adic level `e`**:
in degree `n` the group `Γ((X, T(n)_e, δ(n)), F)` with the `D(n)`-module structure of
`levelSectionsModule`, with the restriction maps of `F` along the transition maps of the system of
[Stacks, Tag 07JN] as its structure maps.

This is `levelSectionsData` read as a `Crystalline.CosimplicialModule` through
`Crystalline.SemilinearCosimplicialModule.toCosimplicialModule`, and it is the `L_*` the
hypothesis `hiso` of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` quantifies
over.  The isomorphism that hypothesis asks for is **not** constructed here. -/
def levelSectionsCosimplicialModule : CosimplicialModule (wholeSpaceEnvelopeRing hp) :=
  (levelSectionsData hp F e).toCosimplicialModule

/-- **The degree `n` of `L_*` is the group of sections of `F` over `(X, T(n)_e, δ(n))`.** -/
theorem levelSectionsCosimplicialModule_obj (n : SimplexCategory) :
    ((levelSectionsCosimplicialModule hp F e).obj (op (op n)) : Type u) =
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u) :=
  rfl

/-- **The structure map of `L_*` along `φ : ⦋n⦌ ⟶ ⦋m⦌` is the restriction map of `F`** along the
transition map `T(m)_e ⟶ T(n)_e` of the system of [Stacks, Tag 07JN]. -/
theorem levelSectionsCosimplicialModule_map_apply {n m : SimplexCategory} (φ : n ⟶ m)
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    (levelSectionsCosimplicialModule hp F e).map φ.op.op x =
      F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op x :=
  rfl

/-- The degree `n` of the underlying cosimplicial abelian group of `L_*` is the group of sections
of `F` over `(X, T(n)_e, δ(n))`.  This is the form in which the isomorphism `ε` of the hypothesis
`hiso` of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` meets `L_*`. -/
theorem levelSectionsCosimplicialModule_forget_obj (n : SimplexCategory) :
    ((((cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
        (levelSectionsCosimplicialModule hp F e)).obj n : Type u)) =
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u) :=
  rfl

/-- The structure map of the underlying cosimplicial abelian group of `L_*` along
`φ : ⦋n⦌ ⟶ ⦋m⦌` is the restriction map of `F` along the transition map `T(m)_e ⟶ T(n)_e` of the
system of [Stacks, Tag 07JN]. -/
theorem levelSectionsCosimplicialModule_forget_map_apply {n m : SimplexCategory} (φ : n ⟶ m)
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    ((((cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
        (levelSectionsCosimplicialModule hp F e)).map φ).hom x) =
      F.val.map (((wholeSpaceSystem S hp).map φ.op).app e).op x :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

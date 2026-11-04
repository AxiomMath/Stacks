module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionLocalizes
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitAcyclicity

/-!
# The sheafification unit is an isomorphism on the level objects, uniformly in the degree

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, and let `F` be a
locally quasi-coherent sheaf of `𝒪_{X/S}`-modules.  The first equality of the source's proof of
[Stacks, Tag 07LF] is
`...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine`:
over an object `A = (U, T, δ)` of `Cris(X/S)` with `T` affine and lying over an affine open of
the divided power base, the sections of the crystalline sheafification of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the honest tensor product of the sections of the two factors.

That statement is about one object.  This module turns it into a statement about the whole
cosimplicial system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] at once: for every `i` and every
`p`-adic level `e`, the sheafification unit induces an **isomorphism of cosimplicial abelian
groups**

`M(•)_e^{pre}  ≅  M(•)_e`,

the source being the level sections of the presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` and the target the
level sections of its sheafification, which is the cosimplicial group the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` speaks about.

Nothing per-object is left to discharge at the use site.  The two hypotheses `h` and `hV` of the
object-wise statement are **not** per-object: `V` is an open of the *base* scheme `S.S.scheme`,
so `V = ⊤` works for every object at once, `hV` is `AlgebraicGeometry.isAffineOpen_top` from the
standing `[IsAffine S.S.scheme]`, and `h` is `le_rfl` because `Scheme.Hom.preimage_top` is `rfl`.
The one genuinely per-object hypothesis, the affineness of the ambient scheme, holds uniformly
for the level objects of `...SmallSite.wholeSpaceSystem` and is proved here.

## Main definitions

* `...SmallSite.levelCosimplicialSectionsMap` — **functoriality of
  `...SmallSite.levelCosimplicialSections` in its presheaf argument**: a morphism `η : G ⟶ G'` of
  abelian presheaves on `Cris(X/S)` induces a morphism of cosimplicial abelian groups
  `M(•)_e(G) ⟶ M(•)_e(G')`, whose component in degree `n` is `η` at the object `T(n)_e`.
* `...SmallSite.levelCosimplicialSectionsMapIso` — the same morphism when every one of those
  components is bijective, packaged as an **isomorphism**, so that its inverse and the naturality
  of the inverse are available.
* `...SmallSite.levelCosimplicialSectionsSheafifyIso` — **the main result**, see below.

## Main results

* `...SmallSite.isIso_levelCosimplicialSectionsMap` — a pointwise isomorphism of presheaves
  induces an isomorphism of the cosimplicial groups of level sections.
* `...SmallSite.isAffine_wholeSpaceSystem_target` — **the ambient scheme of every level object
  `(X, T(n)_e, δ(n))` is affine**, uniformly in `(n, e)`.  This is
  `...SmallSite.isWholeSpaceSystem_wholeSpaceSystem` — the system lies in the chaotic subsite
  `𝒞` of [Stacks, Tag 07JK] — followed by `...SmallSite.isAffineObject_of_isOverWholeSpace`,
  which says that an object of `𝒞` over an affine `X` is an affine object of `Cris(X/S)`.
* `...SmallSite.levelCosimplicialSectionsSheafifyIso` — **the sheafification unit is an
  isomorphism of cosimplicial abelian groups at every level.**  For a locally quasi-coherent `F`,
  every `i` and every `p`-adic level `e`, the morphism induced by
  `CategoryTheory.toSheafify` is an isomorphism

  `M(•)_e(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})  ≅  M(•)_e((F ⊗_{𝒪_{X/S}} Ω^i_{X/S})^#)`

  of cosimplicial abelian groups, with `...SmallSite.levelCosimplicialSectionsSheafifyIso_hom_app`
  computing its degree-`n` component as the sheafification unit at `T(n)_e`.

## Implementation notes

**Naturality in the cosimplicial direction is naturality of `CategoryTheory.toSheafify` in the
site object, and nothing more.**  `CategoryTheory.toSheafify` is the unit of the sheafification
adjunction, hence a genuine natural transformation of presheaves, so the cosimplicial square is
`CategoryTheory.NatTrans.naturality` at the structure map `T(n)_e ⟶ T(m)_e` of the system.  The
superficially relevant `CategoryTheory.toSheafify_naturality` is naturality in the *presheaf*
variable and is not what is used.

**The pointwise-isomorphism step is stated with a `Function.Bijective` hypothesis** because that
is the shape the first equality is available in; it is converted by
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`, which applies because the forgetful
functor of `AddCommGrpCat` reflects isomorphisms, and then
`CategoryTheory.NatIso.isIso_of_isIso_app` promotes the degreewise isomorphisms to an isomorphism
of functors out of `SimplexCategory`.  Passing from an object `n` of `SimplexCategory` to the
natural number `n.len` costs nothing: `SimplexCategory.mk_len` is `rfl`.

**The target of the main isomorphism is spelled `(tensorDifferentialFormsSheaf F i).obj`**, which
is the spelling `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` uses; it is the
underlying presheaf of the sheaf, equal to `CategoryTheory.sheafify` of
`...SmallSite.tensorDifferentialFormsPresheaf F i` by `rfl`
(`...SmallSite.tensorDifferentialFormsSheaf_obj`).

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved here.**  What is proved is one
of the three ingredients of the isomorphism `ε` that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for: the sheafification half,
in cosimplicial form.  The cosimplicial module `L_*` is not constructed here, the second equality
`M(n)_e ⊗_{D(n)_e} Ω^i_{D(n)_e} = M(n)_e ⊗_{D(n)} Ω^i_{D(n)}` is not transported here, and the
two are not composed here.

The hypotheses carried are exactly those the pieces need: `hp : IsNilpotent (S.p : Γ(S.X, ⊤))`,
`[IsAffine S.X]`, `[IsAffine S.S.scheme]` and the local quasi-coherence of `F`, which is
hypothesis (1) of [Stacks, Tag 07JN].  Hypothesis (2) of [Stacks, Tag 07JN] is **not** assumed,
and neither is any flatness or finiteness.

**This retires a claim made in the "What `ε` owes" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorRestrictionVanishing.lean`**, namely
that the sheafification bijection is available only object by object and has no uniform-in-`n`
form, so that the cosimplicial naturality of that comparison was still owed.  It is available
uniformly in `n`, it is available as an isomorphism rather than a family of bijections, and its
cosimplicial naturality is the naturality of the adjunction unit.  The cosimplicial naturality
of `Crystalline.tensorFormsCompletionLevelEquiv`, the other comparison that note lists, is
untouched here; it is
`Crystalline.tensorFormsCompletionLevelEquivAt_naturality` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelFormsNaturality.lean`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Functoriality of the level sections in the presheaf -/

/-- **`...SmallSite.levelCosimplicialSections` is functorial in its presheaf argument.**  A
morphism `η : G ⟶ G'` of abelian presheaves on `Cris(X/S)` induces a morphism

`M(•)_e(G) ⟶ M(•)_e(G')`

of cosimplicial abelian groups, whose component in degree `n` is `η` evaluated at the object
`T(n)_e` of the system.  Naturality in the cosimplicial direction is naturality of `η` at the
structure maps of the system, so nothing is assumed of `T`. -/
def levelCosimplicialSectionsMap (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {G G' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : G ⟶ G') (e : ℕ) :
    levelCosimplicialSections T G e ⟶ levelCosimplicialSections T G' e where
  app n := η.app (op ((T.obj (op n)).obj e))
  naturality _ _ _ := η.naturality _

/-- **The degree-`n` component of `...SmallSite.levelCosimplicialSectionsMap`** is `η` at the
object `(X, T(n)_e, δ(n))`. -/
theorem levelCosimplicialSectionsMap_app (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {G G' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : G ⟶ G') (e n : ℕ) :
    (levelCosimplicialSectionsMap T η e).app ⦋n⦌ = η.app (op ((T.obj (op ⦋n⦌)).obj e)) :=
  rfl

/-- **A degreewise isomorphism of level sections is an isomorphism of cosimplicial groups.**  If
`η : G ⟶ G'` is an isomorphism at every object `T(n)_e` of the system, then the induced morphism
`M(•)_e(G) ⟶ M(•)_e(G')` is an isomorphism, by
`CategoryTheory.NatIso.isIso_of_isIso_app`. -/
theorem isIso_levelCosimplicialSectionsMap (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {G G' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : G ⟶ G') (e : ℕ)
    (h : ∀ n : ℕ, IsIso (η.app (op ((T.obj (op ⦋n⦌)).obj e)))) :
    IsIso (levelCosimplicialSectionsMap T η e) :=
  have : ∀ n : SimplexCategory, IsIso ((levelCosimplicialSectionsMap T η e).app n) :=
    fun n => h n.len
  NatIso.isIso_of_isIso_app _

/-- **`...SmallSite.levelCosimplicialSectionsMap` as an isomorphism**, when `η` is bijective on
the sections over every object `T(n)_e` of the system.  This is the shape the consumer needs: it
has the inverse morphism of cosimplicial objects, and with it the naturality of the inverse in
the cosimplicial direction. -/
noncomputable def levelCosimplicialSectionsMapIso
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {G G' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : G ⟶ G') (e : ℕ)
    (h : ∀ n : ℕ, Function.Bijective (ConcreteCategory.hom
      (η.app (op ((T.obj (op ⦋n⦌)).obj e))))) :
    levelCosimplicialSections T G e ≅ levelCosimplicialSections T G' e :=
  haveI := isIso_levelCosimplicialSectionsMap T η e fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h n)
  asIso (levelCosimplicialSectionsMap T η e)

/-- The forward direction of `...SmallSite.levelCosimplicialSectionsMapIso` is the morphism it
was built from. -/
theorem levelCosimplicialSectionsMapIso_hom
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {G G' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : G ⟶ G') (e : ℕ)
    (h : ∀ n : ℕ, Function.Bijective (ConcreteCategory.hom
      (η.app (op ((T.obj (op ⦋n⦌)).obj e))))) :
    (levelCosimplicialSectionsMapIso T η e h).hom = levelCosimplicialSectionsMap T η e :=
  rfl

/-! ### The level objects of the whole-space system are affine -/

section Affine

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The ambient scheme of every object of the system `(X, T(n)_e, δ(n))` is affine**, uniformly
in the cosimplicial degree `n` and the `p`-adic level `e`.

The system lies in the chaotic subsite `𝒞` of [Stacks, Tag 07JK] by
`...SmallSite.isWholeSpaceSystem_wholeSpaceSystem`, and an object of `𝒞` over an affine `X` is an
affine object of `Cris(X/S)` by `...SmallSite.isAffineObject_of_isOverWholeSpace`; the second
component of that conjunction is the affineness of the ambient scheme.

This is the only per-object hypothesis of
`...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine`. -/
theorem isAffine_wholeSpaceSystem_target (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (n e : ℕ) :
    IsAffine (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj.thickening.target.scheme :=
  (isAffineObject_of_isOverWholeSpace _ (isWholeSpaceSystem_wholeSpaceSystem S hp n e)).2

/-! ### The sheafification unit on the level sections -/

/-- **The sheafification unit is an isomorphism of cosimplicial abelian groups at every level.**

For a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules `F`, every `i` and every `p`-adic level
`e`, the morphism `CategoryTheory.toSheafify` induces an isomorphism

`M(•)_e(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})  ≅  M(•)_e((F ⊗_{𝒪_{X/S}} Ω^i_{X/S})^#)`

of cosimplicial abelian groups over the system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN].

This is the first equality of the source's proof of [Stacks, Tag 07LF],
`...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine`, in the
cosimplicial form that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` consumes.  Its two non-affineness
hypotheses are discharged once for all objects — `V = ⊤` on the *base* scheme, affine by
`AlgebraicGeometry.isAffineOpen_top`, and `h = le_rfl` because `Scheme.Hom.preimage_top` is
`rfl` — and the affineness of the ambient schemes is
`...SmallSite.isAffine_wholeSpaceSystem_target`.  **No tag attribute is placed.** -/
noncomputable def levelCosimplicialSectionsSheafifyIso (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F) (i e : ℕ) :
    levelCosimplicialSections (wholeSpaceSystem S hp) (tensorDifferentialFormsPresheaf F i) e ≅
      levelCosimplicialSections (wholeSpaceSystem S hp) (tensorDifferentialFormsSheaf F i).obj e :=
  levelCosimplicialSectionsMapIso (wholeSpaceSystem S hp)
    (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) e fun n =>
      haveI := isAffine_wholeSpaceSystem_target hp n e
      bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine
        le_rfl (isAffineOpen_top S.S.scheme) hF

/-- **The degree-`n` component of `...SmallSite.levelCosimplicialSectionsSheafifyIso`** is the
sheafification unit of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` at the object `(X, T(n)_e, δ(n))`. -/
theorem levelCosimplicialSectionsSheafifyIso_hom_app (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F) (i e n : ℕ) :
    (levelCosimplicialSectionsSheafifyIso hp F hF i e).hom.app ⦋n⦌ =
      (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) :=
  rfl

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end
